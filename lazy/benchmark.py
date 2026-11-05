#!/usr/bin/env python3
"""Reproduce process-level checking times; never modify the Agda originals."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile
import time


def timed(command, cwd):
    start = time.perf_counter()
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    elapsed = time.perf_counter() - start
    output = result.stdout + result.stderr
    if result.returncode:
        raise RuntimeError(f"Command failed: {command!r}\n{output}")
    return {"seconds": elapsed, "command": command, "output": output}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda-source", type=Path, default=Path.home() / "DOMAIN/LAZY")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("benchmark.json"))
    args = parser.parse_args()
    if args.runs < 1:
        parser.error("--runs must be positive")
    directory = Path(__file__).resolve().parent
    project = directory.parent
    # Build time is excluded; the caller must build first.
    locate = subprocess.run(["cabal", "list-bin", "exe:seg"], cwd=project,
                            text=True, capture_output=True, check=True)
    binary = Path(locate.stdout.strip().splitlines()[-1])
    version = subprocess.run(["agda", "--version"], text=True,
                             capture_output=True, check=True).stdout
    unit = [timed([str(binary), "All.seg"], directory) for _ in range(args.runs)]
    agda = []
    endpoints = ["LAZY.Example4", "LAZY.InvarianceL", "LAZY.InvarianceLBack", "LAZY.ObsInv"]
    for _ in range(args.runs):
        # Each repetition is an independent cold Agda interface build.
        # Only copied sources and temporary interfaces are removed on exit.
        with tempfile.TemporaryDirectory(prefix="lazy-agda-check-") as temporary:
            root = Path(temporary)
            shutil.copytree(args.agda_source, root / "LAZY",
                            ignore=shutil.ignore_patterns("*.agdai", "_build"))
            (root / "All.agda").write_text("module All where\n" +
                "".join(f"import {name}\n" for name in endpoints))
            agda.append(timed(["agda", "--no-libraries", "-i", str(root),
                               str(root / "All.agda")], root))
    report = {
        "method": "Wall time of fresh checking processes; compiler build excluded. "
                  "Unit has no persistent interface cache. Agda uses a fresh source copy per run.",
        "scope_warning": "Different presentations and theorem coverage; these are whole-development "
                         "checking times, not a controlled language-performance comparison.",
        "unit_binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "unit_source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(directory.glob("*.seg")) if not p.name.startswith("Check")},
        "agda_version": version.strip(),
        "agda_source": str(args.agda_source.resolve()),
        "agda_endpoints": endpoints,
        "unit": unit, "agda_cold": agda,
        "unit_median_seconds": statistics.median(r["seconds"] for r in unit),
        "agda_cold_median_seconds": statistics.median(r["seconds"] for r in agda),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Unit median: {report['unit_median_seconds']:.3f} s")
    print(f"Agda cold median: {report['agda_cold_median_seconds']:.3f} s")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
