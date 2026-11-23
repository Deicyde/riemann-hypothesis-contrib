#!/usr/bin/env python3
"""rh-buildq restore: register every known input-hash -> artifact mapping with Lake, once.

usage: pool-restore.py [--ancestor REV] <project-dir> [extra-revision ...]

Collects (public, no credentials) and merges into .lake/rh-buildq-pool.jsonl, first entry wins:
  with --ancestor REV: the map of a successful CI build with REV's exact build inputs
                       (ci/inputs/<fingerprint>.json, else ci/revisions/<REV>.json), checked
                       like scripts/ci-cache-get.py does: receipt bound to the input fingerprint,
                       map and module manifest SHA-256, manifest covering the map exactly. The
                       manifest's per-artifact SHA-256 is checked on every download.
  rh-buildq/pool/<tc>.jsonl              union of everything rh-buildq publishers uploaded
  rh-buildq/maps/<HEAD>.jsonl            this commit's own partial publication (if any)
  revisions/<repo>/tc/<tc>/<sha>.jsonl   stock Lake maps for HEAD, its parents, and extra revisions
                                          (e.g. maps published for a PR head or GitHub's merge commit)
Then, at the same time: `lake cache add` of the mappings not yet registered locally (in
parallel shards; Lake writes one file per mapping) and a curl download of the artifacts missing
locally (fetch-artifacts.py). With --ancestor, Mathlib's cache (`lake exe mathlib/cache get`)
is fetched first, alongside the map downloads. Nothing is unpacked here: `lake build` with
LAKE_RESTORE_ARTIFACTS=true unpacks a module exactly when the module's own input hash is
mapped and its artifact is local; anything else is compiled.

The project must be checked out at the build target; REV is read from Git objects only.

Environment (all optional, set from job.env by run-build.sh):
  MAP_PREFIX       key prefix for the pool and maps (default rh-buildq; tests use their own)
  MAP_NAME         this build's own map is <prefix>/maps/<MAP_NAME>.jsonl (default HEAD)
  POOL_EXTRA_MAPS  space-separated further map keys to merge, e.g. the per-chunk maps of the
                   rh-shard chunks this build requires
  RESTORE_SHARDS   parallel `lake cache add` processes (default 16)
"""
import gzip, hashlib, json, os, re, subprocess, sys, tempfile, time, urllib.error, urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PUBLIC = "https://rh-cache.taucetiproject.org/"
REPO = "leanprover-community/riemann-hypothesis"
SERVICE = "riemann-hypothesis"
SCHEMA = "2026-03-17"
FIELDS = ("source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
HASH = re.compile(r"[0-9a-f]{16}\Z")
ARTIFACT = re.compile(r"[0-9a-f]{16}\.ltar\Z")
T0 = time.time()


def log(msg):
    print(f"pool-restore: [{time.time() - T0:6.1f}s] {msg}", flush=True)


def fetch(key):
    """GET a public key; None on 404. Retries CDN 5xx and transport errors."""
    req = urllib.request.Request(PUBLIC + key, headers={"User-Agent": "rh-buildq/1", "Cache-Control": "no-cache"})
    for attempt in range(6):
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            if e.code < 500 or attempt == 5:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if attempt == 5:
                raise
        time.sleep(5 * 2 ** attempt)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def identity_of(P, rev):
    """ci-cache-get.py's build-input identity, read from REV's Git objects instead of the tree."""
    show = lambda path: subprocess.check_output(["git", "-C", str(P), "cat-file", "blob", f"{rev}:{path}"])
    ident = {"source_tree": subprocess.check_output(["git", "-C", str(P), "rev-parse", f"{rev}:src"], text=True).strip(),
             "build_roots": {}, "lakefile_sha256": digest(show("lakefile.toml")),
             "manifest_sha256": digest(show("lake-manifest.json")),
             "toolchain": show("lean-toolchain").decode().strip()}
    return ident, digest(canonical({k: ident[k] for k in FIELDS}))


def ci_record(P, rev):
    """A successful CI receipt for REV's build inputs, or None (the checks of ci-cache-get.py)."""
    ident, fp = identity_of(P, rev)
    for key in (f"ci/inputs/{fp}.json", f"ci/revisions/{rev}.json"):
        data = fetch(key)
        if data is None:
            continue
        rec = json.loads(data)
        if (not isinstance(rec, dict) or rec.get("schema") != 1 or rec.get("repository") != REPO
                or rec.get("build_exit_code") != 0 or any(rec.get(k) != ident[k] for k in FIELDS)):
            log(f"{key}: not a successful record for these build inputs")
            continue
        if rec.get("input_fingerprint") != fp:
            raise ValueError(f"{key}: input fingerprint mismatch")
        for field, prefix, suffix in (("map", "ci/maps/", ".jsonl"), ("module_manifest", "ci/module-manifests/", ".jsonl.gz")):
            sha = rec.get(field + "_sha256")
            if not isinstance(sha, str) or not SHA256.fullmatch(sha) or rec.get(field + "_key") != prefix + sha + suffix:
                raise ValueError(f"{key}: invalid immutable {field} identity")
        log(f"{key}: successful CI build {rec.get('candidate_head')}")
        return rec, ident, fp
    return None


def ci_map(P, rev):
    """(entries, {artifact: sha256}) of REV's validated CI map, or ({}, {}) if there is none."""
    found = ci_record(P, rev)
    if found is None:
        log(f"no successful CI record for the build inputs of {rev}")
        return {}, {}
    rec, ident, fp = found
    with ThreadPoolExecutor(2) as pool:
        contents, manifest = pool.map(fetch, (rec["map_key"], rec["module_manifest_key"]))
    if contents is None or digest(contents) != rec["map_sha256"]:
        raise ValueError("CI map is missing or corrupt")
    if manifest is None or digest(manifest) != rec["module_manifest_sha256"] or len(manifest) != rec.get("module_manifest_bytes"):
        raise ValueError("CI module manifest is missing or corrupt")
    lines = contents.splitlines()
    if not lines or json.loads(lines[0]) != SCHEMA:
        raise ValueError("unsupported CI map schema")
    entries = {}
    for line in lines[1:]:
        k, v = json.loads(line)
        if not HASH.fullmatch(k) or not ARTIFACT.fullmatch(v) or k in entries:
            raise ValueError("invalid or duplicate CI map entry")
        entries[k] = v
    rows = gzip.decompress(manifest).splitlines()
    header = json.loads(rows[0])
    if (header.get("schema") != 1 or any(header.get(k) != ident[k] for k in FIELDS)
            or header.get("input_fingerprint") != fp or header.get("map_sha256") != rec["map_sha256"]
            or header.get("modules") != len(entries) or len(rows) - 1 != len(entries)):
        raise ValueError("CI module manifest is not bound to these inputs and this map")
    shas, seen = {}, set()
    for row in rows[1:]:
        name, input_hash, artifact, sha = json.loads(row)
        if input_hash in seen or entries.get(input_hash) != artifact or not SHA256.fullmatch(sha) \
                or shas.setdefault(artifact, sha) != sha:
            raise ValueError("CI module manifest does not uniquely cover its map")
        seen.add(input_hash)
    return entries, shas


def write_map(path, entries):
    path.write_text(json.dumps(SCHEMA) + "\n" + "".join(json.dumps([k, v]) + "\n" for k, v in sorted(entries.items())))


def mathlib_get(P):
    env = dict(os.environ, MATHLIB_CACHE_GET_URL=os.environ.get("MATHLIB_CACHE_GET_URL", "https://cache.mathlib.org/mathlib4"))
    for attempt in range(1, 4):
        if subprocess.run(["lake", "exe", "mathlib/cache", "get"], cwd=P, env=env, stdin=subprocess.DEVNULL).returncode == 0:
            return True
        log(f"Mathlib cache get attempt {attempt} failed")
        time.sleep(20)
    return False


def register(P, fresh, env):
    """`lake cache add` in parallel shards. Each mapping is an independent file write in Lake
    (Cache.writeMap), so shards cannot conflict; the first, small shard runs alone so that only
    one process creates the outputs directory and elaborates any lakefile."""
    items = sorted(fresh.items())
    n = max(1, min(int(os.environ.get("RESTORE_SHARDS", "16")), len(items) // 2000 or 1))
    cmd = ["lake", "cache", "add", "--service", SERVICE, "--repo", REPO]
    with tempfile.TemporaryDirectory(prefix="pool-add-", dir=P / ".lake") as t:
        first, rest = items[:100], items[100:]
        write_map(Path(t) / "0.jsonl", dict(first))
        subprocess.run([*cmd, str(Path(t) / "0.jsonl")], cwd=P, env=env, check=True)
        procs = []
        for i in range(n):
            part = rest[i::n]
            if part:
                f = Path(t) / f"{i + 1}.jsonl"
                write_map(f, dict(part))
                procs.append(subprocess.Popen([*cmd, str(f)], cwd=P, env=env))
        codes = [p.wait() for p in procs]
        if any(codes):
            raise subprocess.CalledProcessError(max(codes), cmd)
    return n


def main():
    args = sys.argv[1:]
    ancestor = None
    if args[:1] == ["--ancestor"]:
        ancestor, args = args[1] or None, args[2:]
    P = Path(args[0]).resolve()
    extra = args[1:]
    (P / ".lake").mkdir(exist_ok=True)   # a fresh clone without an ancestor restore has no .lake yet
    with ThreadPoolExecutor(1) as mathlib:
        ml = mathlib.submit(mathlib_get, P) if ancestor else None
        tc = (P / "lean-toolchain").read_text().strip()
        tcdir = tc.replace("/", "--").replace(":", "---")
        git = lambda *a: subprocess.check_output(["git", "-C", str(P), *a], text=True).split()
        head = git("rev-parse", "HEAD")[0]
        revs = git("rev-list", "--parents", "-n", "1", "HEAD") + extra
        prefix = os.environ.get("MAP_PREFIX") or "rh-buildq"
        keys = [f"{prefix}/pool/{tcdir}.jsonl", f"{prefix}/maps/{head}.jsonl"]
        if os.environ.get("MAP_NAME"):
            keys.append(f"{prefix}/maps/{os.environ['MAP_NAME']}.jsonl")
        keys += os.environ.get("POOL_EXTRA_MAPS", "").split()
        keys += [f"revisions/{REPO}/tc/{tcdir}/{r}.jsonl" for r in dict.fromkeys(revs)]
        with ThreadPoolExecutor(8) as pool:
            ci = pool.submit(ci_map, P, ancestor) if ancestor else None
            blobs = list(pool.map(fetch, keys))
            try:
                merged, shas = ci.result() if ci else ({}, {})
            except Exception as e:   # a corrupt receipt must not stop the other maps from restoring
                log(f"ERROR: ancestor CI map rejected ({e}); continuing without it")
                merged, shas = {}, {}
        if ancestor:
            log(f"ancestor {ancestor}: {len(merged)} CI mappings")
        for key, data in zip(keys, blobs):
            if not data:
                log(f"{key}: none")
                continue
            lines = data.decode().splitlines()
            if not lines or json.loads(lines[0]) != SCHEMA:
                log(f"{key}: unexpected schema, skipped")
                continue
            n = 0
            for l in lines[1:]:
                if l:
                    k, v = json.loads(l)
                    if k not in merged:
                        merged[k] = v; n += 1
            log(f"{key}: {len(lines) - 1} entries ({n} new)")
        out = P / ".lake/rh-buildq-pool.jsonl"
        write_map(out, merged)
        log(f"{len(merged)} mappings in total")
        if not merged:
            if ml:
                ml.result()
            return
        cache = P / ".lake/cache"
        fetch_cmd = [sys.executable, "-I", str(Path(__file__).with_name("fetch-artifacts.py")), str(out), str(cache)]
        if shas:
            (P / ".lake/rh-buildq-sha256.json").write_text(json.dumps(shas))
            fetch_cmd += ["--sha256", str(P / ".lake/rh-buildq-sha256.json")]
        downloads = subprocess.Popen(fetch_cmd)
        env = dict(os.environ, LAKE_CACHE_DIR=str(cache), LAKE_CONFIG=str(P / "lakefile.toml"))
        env.pop("LAKE_ARTIFACT_CACHE", None)
        if ml:
            ok = ml.result()
            log("Mathlib cache " + ("restored" if ok else "NOT restored; Lake will build Mathlib"))
    # On a warm tree register only new mappings (Lake keeps one
    # .lake/cache/outputs/<scope>/<input-hash>.json per mapping).
    have = set()
    for d in (cache / "outputs").glob("*"):
        if d.is_dir():
            have.update(f.name[:-5] for f in os.scandir(d) if f.name.endswith(".json"))
    fresh = {k: v for k, v in merged.items() if k not in have}
    log(f"registering {len(fresh)} mappings not yet registered locally")
    failed = False
    if fresh:
        try:
            shards = register(P, fresh, env)
            log(f"registered {len(fresh)} mappings ({shards} parallel lake cache add)")
        except (OSError, subprocess.CalledProcessError) as e:
            log(f"ERROR: lake cache add failed ({e})"); failed = True
    code = downloads.wait()
    log(f"artifact downloads finished (exit {code})")
    sys.exit(1 if failed else code)


if __name__ == "__main__":
    main()
