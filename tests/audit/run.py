#!/usr/bin/env python3
"""Deterministic adversarial tests, independent of #fails and summary filtering.

Every negative case is a separate process. Positive controls distinguish a
real rejection from broken syntax or an unusable test setup. Reports retain
the source, full diagnostics, exit status, and checker/source hashes.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = "level a b ;\ndata N = z | s (n : N) ;\ndata Empty = ;\n"


def cases():
    # Constructor separation, beta reduction, closures and instantiation.
    for i, j in itertools.product(range(5), repeat=2):
        ni = "(" + "s (" * i + "z" + ")" * i + ")"
        nj = "(" + "s (" * j + "z" + ")" * j + ")"
        wrappers = {
            "direct": ("", ni, nj, "N"),
            "beta": ("id (x : N) : N = x ;\n", f"id {ni}", nj, "N"),
            "closure": ("module M (n : N) { f : N -> N = \\ x -> n ; } ;\n",
                        f"M[{ni}].f", f"M[{nj}].f", "(N -> N)"),
            "nested": ("module M (n : N) { module K { f : N -> N = \\ x -> n ; } ; } ;\n",
                       f"M[{ni}].K.f", f"M[{nj}].K.f", "(N -> N)"),
            "record": ("record Box { value : N ; } ;\n",
                       f"new Box[{ni}]", f"new Box[{nj}]", "Box"),
        }
        for kind, (setup, x, y, typ) in wrappers.items():
            yield f"conversion-{kind}-{i}-{j}", i == j, BASE + setup + f"test : Id {typ} ({x}) ({y}) = refl ({x}) ;\n"

    # All combinations of supplied order assumptions and a demanded lift.
    levels = ["a", "a+", "a++", "b", "b+", "(a \\/ b)"]
    for assumption in ["", "a < b", "b < a", "a = b", "a <= b"]:
        valuations = [(a, b) for a in range(7) for b in range(7)
                      if not assumption or eval(assumption.replace("=", "==")
                          if assumption == "a = b" else assumption, {}, {"a": a, "b": b})]
        def value(term, a, b):
            if "\\/" in term:
                return max(a, b)
            return {"a": a, "b": b}[term[0]] + term.count("+")
        for i, source in enumerate(levels):
            for j, target in enumerate(levels):
                # These simple order theories have a natural-number countermodel
                # whenever the inequality is not valid; domain includes offsets.
                good = all(value(source, a, b) < value(target, a, b) for a, b in valuations)
                premise = f"constraint {assumption} ;\n" if assumption else ""
                yield f"universe-{assumption or 'none'}-{i}-{j}", good, BASE + premise + f"test : U {target} = U {source} ;\n"

    accesses = {
        "direct": ("module M { constraint b < a ; up : U a = U b ; } ;", "M.up"),
        "nested": ("module M { constraint b < a ; module K { up : U a = U b ; } ; } ;", "M.K.up"),
        "param": ("module M (c d : Level) { constraint d < c ; up : U c = U d ; } ;", "M[a,b].up"),
        "inner-param": ("module M { constraint b < a ; module K (x : N) { up : U a = U b ; } ; } ;", "M.K[z].up"),
        "alias": ("module M { constraint b < a ; up : U a = U b ; } ; module K = M ;", "K.up"),
        "open": ("module M { constraint b < a ; up : U a = U b ; } ; open M ;", "up"),
    }
    for kind, (setup, expr) in accesses.items():
        for allowed in [False, True]:
            premise = "constraint b < a ;\n" if allowed else ""
            yield f"guard-{kind}-{allowed}", allowed, BASE + premise + setup + f"\ntest : U a = {expr} ;\n"

    for kind, setup, field, good in [
        ("direct", "", "D", True),
        ("w", "", "N -> D", True),
        ("negative", "", "D -> Empty", False),
        ("double-negative", "", "(D -> Empty) -> Empty", False),
        ("alias", "Neg (X : U a) : U a = X -> Empty ;", "Neg D", False),
        ("hidden", "Neg {X : U a} (x : X) : U a = X -> Empty ;", "Neg x", False),
        ("hidden-let", "Neg {X : U a} (x : X) : U a = X -> Empty ;", "let { T : U a = Neg x ; } in T", False),
        ("hidden-beta", "Neg {X : U a} (x : X) : U a = X -> Empty ; id (T : U a) : U a = T ;", "id (Neg x)", False),
        ("hidden-positive-unsupported", "Same {X : U a} (x : X) : U a = X ;", "Same x", False),
    ]:
        yield f"positivity-{kind}", good, BASE + setup + f"\ndata D : U a = c (x : D) (f : {field}) ;\n"

    for name, text, good in [
        ("self", "bad : Empty = bad ;", False),
        ("local-self", "bad : N = let { k : N = k ; } in z ;", False),
        ("empty-elim", "elim : Empty -> N = split { } ;", True),
        ("missing-branch", "f : N -> N = split { z -> z } ;", False),
        ("extra-branch", "data B = yes ; f : N -> N = split { z -> z ; s n -> n ; yes -> z } ;", False),
        ("duplicate-branch", "f : N -> N = split { z -> z ; z -> s z ; s n -> n } ;", False),
        ("duplicate-unchecked-branch", "f : N -> N = split { z -> z ; z -> Empty ; s n -> n } ;", False),
        ("duplicate-constructors", "data Bad = c | c (n : N) ;", False),
        ("wrong-rec-result", "f : N -> Empty = split { z -> z ; s n | r -> r } ;", False),
        ("record-refinement", "record Pack { T : U a ; value : T ; } ; bad : Pack[T := Empty] = new Pack[N,z] ;", False),
        ("record-refinement-positive", "record Pack { T : U a ; value : T ; } ; good : Pack[T := N] = new Pack[N,z] ;", True),
        ("idj", "bad : Empty = idJ N z (\\ y p -> Empty) z z (refl z) ;", False),
    ]:
        yield name, good, BASE + text + "\n"

    for position in ["adjacent", "separated", "nested", "local"]:
        pairs = itertools.product(["N", "Empty"], repeat=2) if position == "adjacent" else [("N", "N")]
        for x, y in pairs:
            gap = "extra : N ;" if position == "separated" else ""
            record = f"sig {{ T : U a ; {gap} T : U a ; value : T }}"
            if position == "nested":
                record = f"sig {{ inner : {record} }}"
            if position == "local":
                record = f"let {{ S : U a+ = {record} ; }} in S"
            text = BASE + f"R : U a+ = {record} ;\n"
            if position == "adjacent":
                text += f"r : R = struct {{ T = {x} ; T = {y} ; value = z }} ;\ncontradiction : Empty = r.value ;\n"
            yield f"duplicate-fields-{position}-{x}-{y}", False, text


def run(checker, source, args=()):
    start = time.monotonic()
    try:
        r = subprocess.run([str(checker), str(source), *args], capture_output=True,
                           text=True, timeout=3)
        return {"returncode": r.returncode, "stdout": r.stdout, "stderr": r.stderr,
                "seconds": time.monotonic()-start,
                "accepted": r.returncode == 0 and r.stdout.rstrip().endswith("OK")}
    except subprocess.TimeoutExpired:
        return {"accepted": False, "timeout": True, "seconds": time.monotonic()-start}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", type=Path)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    checker = args.checker or Path(subprocess.check_output(
        ["cabal", "list-bin", "exe:seg"], cwd=ROOT, text=True).strip())
    args.out.mkdir(parents=True, exist_ok=True)
    result = []
    with tempfile.TemporaryDirectory(prefix="unit-audit-") as temp:
        for idx, (name, expected, text) in enumerate(cases()):
            p = Path(temp)/f"case{idx}.seg"
            p.write_text(text)
            r = run(checker, p)
            r.update(name=name, expected=expected, source=text)
            r["match"] = r["accepted"] == expected and not r.get("timeout")
            if not r["match"]:
                repro = args.out/f"case{idx}.seg"
                repro.write_text(text)
                print(f"MISMATCH {name}: expected {expected}; {repro}", flush=True)
            result.append(r)
    report = {"checker": str(checker),
              "checker_sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
              "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in [*ROOT.glob("src/*.hs"), *ROOT.glob("app/*.hs")]},
              "cases": result}
    (args.out/"results.json").write_text(json.dumps(report, indent=2))
    print(f"{len(result)} cases; {sum(not r['match'] for r in result)} mismatches")
    raise SystemExit(1 if any(not r["match"] for r in result) else 0)


if __name__ == "__main__":
    main()
