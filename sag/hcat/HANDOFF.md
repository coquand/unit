# HANDOFF: porting ~/AGDA to Unit (sag/hcat)

Read `DESIGN.md` in this directory first. It is the plan. This file gives the working rules and the order of work.

## Task

Port the Agda development `~/AGDA`, which proves Lemma 26 from the Sattler–Wärn axioms, to Unit in `unit/sag/hcat`. Follow milestones M0–M5 of `DESIGN.md`, then continue with M6 (Segal for all n) and M7 (fully faithful functors).

Work autonomously, milestone by milestone, without waiting for the user between milestones. At the end of each milestone:
1. Update the Status section of `DESIGN.md` with the check figures.
2. Update `README.txt`, which you create, listing the files and their main statements.
3. Continue with the next milestone in the same turn.

End the turn only when M5 is finished, when M7 is finished if you continue past M5, or when a condition of "When to stop and ask" is met.

## Rulings by the user (do not revisit)

- **Plain dependent type theory.** There is no judgemental shortcut for Cat: no strict associativity or unit laws of functor composition, and no Licata-style trick.
- **Cat is infinitely coherent,** as an external schema. Coherence levels are nested segment parameters, as in `DESIGN.md`.
- **No new axioms beyond the axiom system.** Every axiom is a segment parameter; nothing is postulated. The three candidate postulates (`𝕀-hom-contr`, `segal-coface-01`, `segal-coface-12`) start as parameters and should be proved if possible.
- **Tactics become lemmas.** Port the Agda solvers as theorems stated once and cited by name, not as procedures to rerun.

## Standing rules (from the user's memory)

- **Shell commands:** every command finishes in under 60 s; use `timeout 55`. A run that needs longer is split.
- **Checking:**
  - from `unit/`, run `./segc sag/hcat changed`, `./segc sag/hcat all`, and `./segc sag/hcat stop` at the end of each session;
  - a fresh check is `SEG=$(cabal list-bin exe:seg); "$SEG" sag/hcat/All.seg --opened`;
  - each file is under 1 s, and each declaration under the 10 s budget. An overrun is a defect to fix, not a wait.
- **Writing:** follow `~/CANONICITY/seg/WRITING.md`:
  - the informal proof comes first, in the file comment;
  - each notion has one name;
  - "by definition" facts are `refl` lemmas;
  - a construction is locked after its characterising lemmas;
  - check `--opened` after each declaration.
- **Reuse, never copy.** Foundations come from `unit/sag/sip` by relative symlinks (`Prelude`, `Paths`, `Axioms`, `FunExtUA`, `Truncation`, …). Look at `unit/sag/categories` and `unit/sag/fpalg` for how `All.seg` and `Theory` are laid out.
- **Name pitfalls in Unit:**
  - no shadowing, including across files linked into one tree;
  - `U` and `Universal` are taken;
  - `normal` is a keyword;
  - no primes in identifiers;
  - opens are not re-exported;
  - the earlier open wins.
- **Git:** no commits and no pushes unless the user asks.
- **Wording:** in reports say "no new axioms" and name the `Theory` parameters (`univ`, `images`, `surjections`) and the axiom-system parameters. Never say "no axioms".
- **Notes:** concise, with no failed attempts and no jargon. Every PDF is stamped with its file name and date.

## Order of work

1. **Inspect.** Read `~/AGDA/README.md` and `~/AGDA/HANDOFF-lemma26-overview.md`. Read `Foundations/Spartan.agda` and `Category/CatAxioms.agda`, and check what `sag/sip` already provides.
2. **M0–M1.** Write `All.seg` with the nested segments `Theory`, `Wild`, `Structure` and `Coh2`, the foundations, `WildCat`, `CatCoherence`, `Cayley`, `GroupoidWords`, `MacLane` and `Pasting`. Check after each file.
3. **M2–M5** in the order of `DESIGN.md`. Port statements faithfully. Restructure proofs where `--opened` shows unexplained openings, and record the reason in the file comment.
4. **After M5,** fill in the "Measuring the levels" table: the innermost segment each main theorem needs.
5. **M6, then M7.**

## When to stop and ask

- An axiom of the system turns out to be insufficient, or seems to need a shortcut.
- A theorem appears to need coherence level 3 or higher. Record which theorem and why, then ask before adding `Coh3`.
- A file cannot be brought under 1 s after restructuring.
- A design choice in `DESIGN.md` turns out to be wrong.

## Report when the turn ends (port finished, or a stop condition)

State:
- what checks, with the module count, declaration count, failures and time;
- the levels table so far;
- open problems.

Stop the server.
