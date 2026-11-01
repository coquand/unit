Unit adversarial audit, 2026-11-01
=================================

The audit found a soundness defect in anonymous records, missing label
validation, and five cases where partial/incremental checking returned OK
although a fresh full check rejected the same program. The fixes are in
src/SegParse.hs and app/Main.hs. No mathematical development was edited.

1. Anonymous records with repeated field labels (soundness)
----------------------------------------------------------
The original checker accepts this entire program, without term parameters:

  level a ;
  data N = z ;
  data Empty = ;
  R : U a+ = sig { T : U a ; T : U a ; value : T } ;
  r : R = struct { T = Empty ; T = N ; value = z } ;
  contradiction : Empty = r.value ;
  #normal contradiction ;

It reports zero failures and normalizes contradiction to z.

Construction checks the fields from left to right. The second T shadows
the first, so value is checked at N. Projection finds the first T by name,
so the inferred type of r.value is Empty. This breaks preservation of
typing under reduction, and proves an empty type without assumptions.

Repair: reject repeated sig and struct labels during resolution, before
elaboration. Tests include adjacent and separated repetitions, nested
records, local definitions, and positive controls with unique labels.
Reusing a label in distinct records remains permitted.

2. Repeated split branches and constructor labels (validation)
------------------------------------------------------------
The original checker also accepts:

  data N = z | s (n : N) ; data Empty = ;
  f : N -> N = split { z -> z ; z -> Empty ; s n -> n } ;

Only the first z branch is checked and executed. The ill-typed second
branch is ignored. This is not a second proof of Empty: the untyped code
is unreachable under the evaluator's first-match rule. Duplicate data
constructor names were also accepted.

Repair: reject repeated constructor labels, branch labels and named
pattern/recursive-result binders. Repeated anonymous patterns (_) remain
valid. examples/unique-labels.seg records the regressions and controls.

3. Partial/incremental checking can omit required checks
------------------------------------------------------
driver.py reproduces these five cases in disposable directories:

  each-root
    --each checked imported modules but omitted declarations in All.seg.
    Repair: include the entry file and assign each event to one file.

  changed-first-root
    On the first changed request, the server marked imported files dirty
    but not All.seg. Invalid entry-file declarations were never checked.
    Repair: include the entry file in the initial dirty set.

  changed-root-dependent
    After an imported declaration changed type, changed omitted the
    unchanged entry file that depended on that declaration.
    Repair: include the entry file in dependency closure.

  import-line-edit
    The content key discarded entire lines beginning with import. Editing
    a declaration after the import's semicolon could leave the key equal.
    Repair: retain import lines in content keys, remove only import
    statements from dependency tokens, and parse nested imports instead
    of assuming one import per physical line.

  changed-lock
    Changing transparent A.v to opaque A.v in B.seg can invalidate a later
    proof in C.seg. C need not mention B, so the old dependency closure
    omitted it. Repair: compare lock commands and their file order and
    recheck the full development when they change.

These are defects in the checking driver, not further kernel derivations
of Empty. Each reproduction compares the incremental result with a fresh,
unfiltered run. The server is terminated in a finally block after each
test; the runner does not contact the development's existing servers.

Systematic coverage
-------------------
run.py generates 345 distinct programs:
  - constructor separation and beta conversion;
  - closures under distinct module and nested-module instantiations;
  - record construction and refinements;
  - universe lifts under five elementary order theories;
  - module constraints through direct access, nesting, parameters,
    aliases and opens, with and without sufficient ambient hypotheses;
  - direct and hidden negative occurrences in data constructors;
  - recursion, split coverage, identity elimination and duplicate labels.

Expected rejections run as separate processes, not inside #fails.
Successful acceptance requires both exit status zero and a final OK.
Each process has a three-second timeout. A timeout is always a mismatch.
Full sources, stdout, stderr, statuses and executable/source hashes are
written to results.json. The runners exit nonzero on a mismatch.

Before the repairs, 7 of the 345 generated cases were unexpectedly
accepted (several are variations of the same record defect), and all five
driver comparisons disagreed. After the repairs, both suites pass.
evidence.json retains the before/after summaries and failing examples.

Reproduce from unit/ (each command is intended to finish within 55 s):

  timeout 55 cabal build exe:seg --offline
  timeout 55 python3 tests/audit/run.py --out /tmp/unit-audit-language
  timeout 55 python3 tests/audit/driver.py --out /tmp/unit-audit-driver
  timeout 55 ./run-tests.sh > /tmp/unit-regressions.txt
  diff -u tests.expected /tmp/unit-regressions.txt

Both runners accept --checker PATH to compare another executable.
An already-running server still uses its old executable: restart it before
relying on the repaired driver. No commits or pushes were made.

Development validation
----------------------
The existing regression output matches tests.expected, with the new
20-declaration unique-labels example added. The deliberate failures in
locks.seg and unfilled.seg remain unchanged.

Fresh development checks:
  core: three batches, 9650 + 4720 + 3650 declarations, zero failures;
        28.49 s, 14.82 s, 16.72 s CPU respectively. The original single
        run hit the 55-second wall-clock limit, so the check was split.
        The event inventory confirms that these selections cover all
        18016 declarations (four are selected in two batches), with none
        omitted. No proof definitions were changed.
  sag/chatelet: 15770 declarations, zero failures, 7.36 s.
  sag/hcat-segal: 2876 declarations, zero failures, 3.32 s (--opened).
  sag/hcat: a fresh full check passes; see evidence.json for its summary.

Limits
------
This is a bounded adversarial audit, not a soundness proof. The universe
tests cover simple finite families; they are not an independent proof of
the general level solver. The existing opaque-type/etaV diagnostic in
doc/etav-lock-diagnostic.txt is a separate previously reported issue and
was not repaired here. The prior guard and hidden-positivity fixes were
exercised; no bypass was found in these generated variants. Future work
should expand generated dependent telescopes, read-back/substitution
tests, and fresh-versus-incremental comparisons beyond these examples.
