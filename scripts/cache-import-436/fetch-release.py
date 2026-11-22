#!/usr/bin/env python3
"""Stream the pinned volunteer archive, checking every part and every file.

No artifact is executed. A receipt is written only after complete verification.
Only one compressed part occupies disk at a time. Extraction has an explicit
size cap; --inspect verifies and counts without keeping uncompressed outputs.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import threading

PINS = Path(__file__).with_name('release.json')
GIB = 1024**3


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def relative(name):
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or '\\' in name or not p.parts or p.parts[0] != 'lean':
        raise ValueError(f'unsafe archive path: {name!r}')
    return p.as_posix()


def download(asset, directory):
    destination = directory / asset['name']
    subprocess.run(['curl', '--disable', '--fail', '--silent', '--show-error', '--location',
                    '--retry', '3', '--max-filesize', str(asset['size']), asset['url'],
                    '--output', str(destination)], check=True)
    if destination.stat().st_size != asset['size'] or digest(destination) != asset['sha256']:
        raise ValueError(f'part failed its pinned size/SHA256: {destination.name}')
    return destination


def manifest(pins, directory):
    asset, = [a for a in pins['assets'] if a['name'] == 'MANIFEST.sha256.zst']
    compressed = download(asset, directory)
    result = {}
    with subprocess.Popen(['zstd', '-dc', str(compressed)], stdout=subprocess.PIPE) as proc:
        for raw in proc.stdout:
            line = raw.decode().rstrip('\n')
            match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
            if not match:
                raise ValueError('malformed per-file manifest')
            sha, name = match.groups()
            name = relative(name)
            if name in result:
                raise ValueError('duplicate manifest member')
            result[name] = sha
        if proc.wait():
            raise ValueError('manifest decompression failed')
    if len(result) != pins['files']:
        raise ValueError('manifest count differs from the pinned release')
    return result


def verify(pins, directory, extract, limit):
    pending = manifest(pins, directory)
    parts = sorted((a for a in pins['assets'] if '.part-' in a['name']), key=lambda a: a['name'])
    failures = []
    combined = hashlib.sha256()
    proc = subprocess.Popen(['zstd', '-dc'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def feed():
        try:
            for asset in parts:
                if shutil.disk_usage(directory).free < asset['size'] + GIB:
                    raise ValueError('insufficient space for one compressed archive part')
                path = download(asset, directory)
                with path.open('rb') as stream:
                    while block := stream.read(1024**2):
                        combined.update(block)
                        proc.stdin.write(block)
                path.unlink()
                print(json.dumps({'verified_part': asset['name']}), flush=True)
            proc.stdin.close()
        except BaseException as e:
            failures.append(e)
            proc.kill()

    worker = threading.Thread(target=feed, daemon=True)
    worker.start()
    count = total = modules = 0
    try:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
            for item in archive:
                name = relative(item.name)
                if item.isdir():
                    continue
                if not item.isfile() or name not in pending:
                    raise ValueError(f'unexpected, duplicate, or non-regular member: {name}')
                total += item.size
                if total > limit:
                    raise ValueError(f'unpacked bytes exceed the explicit {limit // GIB} GiB limit')
                source = archive.extractfile(item)
                target = None
                if extract is not None:
                    path = extract / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    target = path.open('xb')
                sha = hashlib.sha256()
                try:
                    while block := source.read(1024**2):
                        sha.update(block)
                        if target:
                            target.write(block)
                finally:
                    source.close()
                    if target:
                        target.close()
                if sha.hexdigest() != pending.pop(name):
                    raise ValueError(f'extracted file SHA256 mismatch: {name}')
                count += 1
                modules += name.endswith('.olean')
                archive.members.clear()
                if count % 25000 == 0:
                    print(json.dumps({'files': count, 'unpacked_bytes': total}), flush=True)
        # Consume the tar stream's final padding so the download/hash thread can finish.
        while proc.stdout.read(1024**2):
            pass
        worker.join()
        if failures:
            raise failures[0]
        if proc.wait() or pending or modules != pins['modules'] or combined.hexdigest() != pins['archive_sha256']:
            raise ValueError('incomplete archive, module inventory, or combined SHA256 mismatch')
    finally:
        if proc.poll() is None:
            proc.kill()
        proc.stdout.close()
        worker.join(timeout=10)
    return {'schema': 1, 'kind': 'verified-volunteer-artifact-archive',
            'release': pins['release'], 'revision': pins['revision'],
            'archive_sha256': combined.hexdigest(), 'files': count, 'modules': modules,
            'unpacked_bytes': total, 'extraction': str(extract) if extract else None,
            'proof_verification': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True, help='new directory for downloads and receipt')
    p.add_argument('--inspect', action='store_true', help='verify without retaining extracted files')
    p.add_argument('--extract-to', type=Path, help='new directory, separate from download storage')
    p.add_argument('--max-unpacked-gib', type=int, default=112)
    args = p.parse_args()
    if args.inspect == (args.extract_to is not None) or args.max_unpacked_gib <= 0:
        p.error('select exactly one of --inspect or --extract-to, with a positive extraction limit')
    args.output.mkdir(mode=0o700, parents=True, exist_ok=False)
    if args.extract_to:
        args.extract_to.mkdir(mode=0o700, parents=True, exist_ok=False)
        if shutil.disk_usage(args.extract_to).free < (args.max_unpacked_gib + 8) * GIB:
            raise ValueError('extraction filesystem lacks the requested capacity plus 8 GiB reserve')
    receipt = verify(json.loads(PINS.read_text()), args.output.resolve(),
                     args.extract_to.resolve() if args.extract_to else None, args.max_unpacked_gib * GIB)
    (args.output / 'verified-archive.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
