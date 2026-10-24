#!/usr/bin/env python3
"""Check Picard completely; --isolated copies the reachable source closure."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


def sources(root):
    pending = ["All.seg"]
    found = {}
    while pending:
        name = pending.pop()
        if name in found:
            continue
        path = root / name
        data = path.read_bytes()
        found[name] = (path.resolve(), data)
        text = re.sub(r"--[^\n]*", "", data.decode())
        pending.extend(m + ".seg" for m in re.findall(r"\bimport\s+([A-Za-z0-9_-]+)\s*;", text))
    return found


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=Path, default=root.parent /
        "dist-newstyle/build/aarch64-osx/ghc-9.6.7/segd-0.1.0.0/x/segd/build/segd/segd")
    parser.add_argument("--isolated", action="store_true")
    args = parser.parse_args()
    checker = args.checker.resolve()
    closure = sources(root)
    if args.isolated:
        export = Path(tempfile.mkdtemp(prefix="picard-complete-export-"))
        manifest = {}
        for name, (origin, data) in closure.items():
            (export / name).write_bytes(data)
            manifest[name] = {"source": str(origin), "sha256": hashlib.sha256(data).hexdigest()}
        (export / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        root = export
        print(f"Isolated export: {root} ({len(closure)} regular source files)", flush=True)
    result = subprocess.run([str(checker), "All.seg"], cwd=root,
                            capture_output=True, text=True, timeout=60)
    output = result.stdout + result.stderr
    print(output, end="")
    if result.returncode or not re.search(r"All.seg: \d+ declarations, 0 failed,", output) or not output.rstrip().endswith("OK"):
        raise SystemExit("Complete check failed")


if __name__ == "__main__":
    main()
