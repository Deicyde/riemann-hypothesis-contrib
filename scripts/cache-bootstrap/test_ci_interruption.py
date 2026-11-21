#!/usr/bin/env python3
"""Interrupt a real stock build; recover completed raw outputs without elaboration."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time


def main():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("ci_interrupt", here.parent / "ci-build.py")
    ci = importlib.util.module_from_spec(spec); spec.loader.exec_module(ci)
    for partial_pack in (False, True):
        with tempfile.TemporaryDirectory(prefix="rh-interrupt-fixture-") as directory:
            directory = Path(directory)
            root, packages, output, durable = (directory / name for name in ("project", "packages", "staging", "persistent"))
            (root / "src").mkdir(parents=True); packages.mkdir()
            (root / "lean-toolchain").write_text(ci.TOOLCHAIN + "\n")
            (root / "lakefile.toml").write_text('name="interruptFixture"\nsrcDir="src"\nplatformIndependent=true\ndefaultTargets=["Proof"]\n[[lean_lib]]\nname="Proof"\nglobs=["Fast", "Slow"]\n[[lean_lib]]\nname="Extras"\nroots=["Stale", "Corrupt"]\n')
            version = "1.2.0" if ci.TOOLCHAIN.endswith("v4.33.1") else "1.3.0"
            (root / "lake-manifest.json").write_text(json.dumps({"version": version, "packagesDir": ".lake/packages", "packages": []}))
            (root / "src/Fast.lean").write_text("theorem completed : True := True.intro\n")
            (root / "src/Slow.lean").write_text('import Lean\nimport Fast\nrun_elab do\n  IO.FS.writeFile "/work/result/slow-started" "yes"\n  IO.sleep 120000\ntheorem pending : True := completed\n')
            (root / "src/Stale.lean").write_text("def stale : Nat := 1\n")
            (root / "src/Corrupt.lean").write_text("def intact : Nat := 1\n")
            environment = {key: value for key, value in os.environ.items() if not key.startswith("LAKE_") and key != "LEAN_PATH"}
            environment["ELAN_TOOLCHAIN"] = ci.TOOLCHAIN
            subprocess.run(["lake", "build", "+Stale:ltar", "+Corrupt:ltar"], cwd=root, env=environment,
                           stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT, check=True)
            old_parts = {path.relative_to(root / ".lake/build"): path.read_bytes()
                         for path in (root / ".lake/build").rglob("*") if path.is_file() and path.name.startswith(("Stale.", "Corrupt."))}
            lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root, env=environment, text=True).strip())
            hashes = ci.native_hashes(lean.parent.parent, [root / ".lake/build/ir/Stale.ltar", root / ".lake/build/ir/Corrupt.ltar"], directory)
            (root / "src/Stale.lean").write_text("def stale : Nat := 2\n")
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
            git("init", "-q"); git("add", "src", "lakefile.toml", "lean-toolchain", "lake-manifest.json")
            git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture")
            command = [sys.executable, str(here.parent / "ci-build.py"), "--candidate", str(root), "--packages", str(packages),
                       "--output", str(output), "--work-dir", str(durable), "--jobs", "2", "--reserve-disk-gib", "0",
                       "--dependency-manifest-sha256", ci.sha256(root / "lake-manifest.json")]
            with (directory / "controller.log").open("wb") as log:
                process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
                try:
                    deadline = time.monotonic() + 45
                    while time.monotonic() < deadline:
                        runs = list(durable.glob("run-*")) if durable.exists() else []
                        if runs and (runs[0] / "result/slow-started").exists():
                            break
                        if process.poll() is not None:
                            raise AssertionError((directory / "controller.log").read_text() + (output / "build.log").read_text())
                        time.sleep(0.1)
                    else:
                        raise AssertionError("long-module marker was not reached")
                    work = runs[0]
                    fast = work / "project/.lake/build/lib/lean/Fast.olean"
                    assert fast.exists() and (fast.with_suffix(".trace")).exists()
                    original, mtime = fast.read_bytes(), fast.stat().st_mtime_ns
                    archive = work / "project/.lake/build/ir/Fast.ltar"
                    if archive.exists():
                        archive.unlink()
                    if partial_pack:
                        archive.write_bytes(b"truncated pack: arbitrary bytes have a valid hash but are not an LTAR")
                    # Valid old LTAR/cache pairs must NOT override a rejected
                    # current-input check or a rejected raw-output hash check.
                    for relative, data in old_parts.items():
                        destination = work / "project/.lake/build" / relative
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        destination.write_bytes(data)
                    for name in ("Stale", "Corrupt"):
                        destination = work / "cache/artifacts" / (hashes[name + ".ltar"] + ".ltar")
                        destination.write_bytes(old_parts[Path("ir") / (name + ".ltar")])
                    with (work / "project/.lake/build/ir/Corrupt.c").open("ab") as stream:
                        stream.write(b"corrupted after the saved completed trace")
                    process.send_signal(signal.SIGINT)
                    code = process.wait(timeout=45)
                    assert code == 130, (code, (directory / "controller.log").read_text())
                    assert fast.read_bytes() == original and fast.stat().st_mtime_ns == mtime
                    checkpoint = json.loads((work / "checkpoint.json").read_text())
                    assert checkpoint["state"] == "failed" and checkpoint["build_exit_code"] == 130
                    receipt = json.loads((output / "receipt.json").read_text())
                    assert receipt["build_exit_code"] == 130 and len(receipt["artifacts"]) == 1, (receipt, (work / "raw-recovery.log").read_text())
                    assert len(ci.load_map(output / "outputs.jsonl")) == 1
                    decisions = {row["name"]: row["ok"] for row in map(json.loads, (work / "result/raw-recovery.jsonl").read_text().splitlines())}
                    assert decisions == {"Fast": True, "Stale": False, "Corrupt": False}, decisions
                    item = receipt["artifacts"][0]
                    assert (output / "artifacts" / item["file"]).read_bytes() != b"truncated pack: arbitrary bytes have a valid hash but are not an LTAR"
                    # Ordinary workflow cleanup must not remove retained raw work.
                    import shutil
                    shutil.rmtree(output)
                    assert fast.exists() and (work / "build.log").exists()
                finally:
                    if process.poll() is None:
                        process.kill(); process.wait()
    print("PASS interrupt preservation: completed raw proof survives; missing/truncated LTAR repacked by stock no-build recovery; failed checkpoint/log survive staging cleanup")


if __name__ == "__main__":
    main()
