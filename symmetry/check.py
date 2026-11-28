"""Check the chapter sources against the pinned Unit library in temporary directories."""
import argparse
import os
import re
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from posixpath import normpath

ROOT = Path(__file__).resolve().parent
# By default the Unit repository that contains this directory.
UNIT = Path(os.environ.get("UNIT_ROOT", ROOT.parent))
REV = "0b2e95a8dda49de0e7e50ed012c64c6e0a26862d"

def git(*args):
    return subprocess.check_output(["git", "-C", UNIT, *args])

def check_universe_bounds(checker, work, main_source, entry):
    """Require rejection of exactly the deliberately undersized declarations."""
    if entry == "Categories":
        name = "CategoryBounds"
        marker = " import RezkCompletion ;"
        cases = ("presheaves-too-small", "missing-object-level", "missing-arrow-level")
        accepted = 3
    else:
        name = "UniverseBounds"
        marker = " import HomotopyCoequalizer ;"
        cases = ("missing-successor", "missing-join", "missing-constraint", "finite-unrelated",
                 "root-fibre-too-small", "classifier-unrelated", "bicycle-ambient-too-small",
                 "sign-classifier-too-small", "rezk-forgot-presentation-level")
        accepted = 9
    (work / f"{name}.seg").write_bytes((ROOT / "tests" / f"{name}.seg").read_bytes())
    assert main_source.count(marker) == 1
    (work / "All.seg").write_text(main_source.replace(marker, marker + f" import {name} ;"))
    run = subprocess.run([checker, "All.seg"], cwd=work, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    expected = {f"Theory.{name}.{case}" for case in cases}
    failures = re.findall(r"^FAILED: (\S+)", run.stdout, re.MULTILINE)
    if run.returncode != 1 or set(failures) != expected or len(failures) != len(expected):
        raise RuntimeError("Unexpected result from the universe tests\n" + run.stdout)
    print(f"{name} tests passed ({accepted} accepted, {len(cases)} rejected)", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--universe-tests", action="store_true",
                        help="also verify that the checker rejects the invalid universe bounds")
    args = parser.parse_args()
    checker = os.environ.get("UNIT_CHECKER") or subprocess.check_output(
        ["cabal", "list-bin", "exe:seg"], cwd=UNIT, text=True).strip()
    tree = {}
    for entry in git("ls-tree", "-r", REV, "sag", "core").decode().splitlines():
        metadata, path = entry.split("\t")
        mode, _, blob = metadata.split()
        tree[path] = mode, blob

    def source(path):
        mode, blob = tree[path]
        data = git("cat-file", "blob", blob)
        if mode == "120000":
            return source(normpath(str(PurePosixPath(path).parent / data.decode())))
        return data

    for entry, library in [("All", "pi3-s2-postnikov"), ("Categories", "categories"),
                           ("FreeGroups", "freegroup")]:
        with tempfile.TemporaryDirectory(prefix="symmetry-unit-") as temp:
            work = Path(temp)
            main_source = (ROOT / (entry + ".seg")).read_text()
            (work / "All.seg").write_text(main_source)
            imports = re.findall(r"\bimport\s+(\w+)\s*;", re.sub(r"--[^\n]*", "", main_source))
            for name in set(imports):
                filename = name + ".seg"
                local = ROOT / "chapters" / filename
                if local.exists():
                    data = local.read_bytes()
                else:
                    path = f"sag/{library}/{filename}"
                    if path not in tree:
                        path = f"sag/em/{filename}"
                    if path not in tree:
                        path = f"sag/categories/{filename}"
                    if path not in tree:
                        path = f"sag/pi3-s2-postnikov/{filename}"
                    data = source(path)
                (work / filename).write_bytes(data)
            print(entry, flush=True)
            subprocess.run([checker, "All.seg"], cwd=work, check=True)
            if entry in ("All", "Categories") and args.universe_tests:
                check_universe_bounds(checker, work, main_source, entry)

if __name__ == "__main__":
    main()
