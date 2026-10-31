# HANDOFF: sag/hcat M6 and M7

Read in this order:
1. `HANDOFF.md`: the working rules. They still hold.
2. `DESIGN.md`: the plan; the Status section and the levels table are current.
3. `README.txt`: the files and their main statements.

## State (2026-10-31, before M6; M6 and M7 are now done, see DESIGN.md Status)

- M0–M5 are done. `./segc sag/hcat all`: 74 modules, 1407 declarations, 0 failed, 6.2 s. Every file is under 1 s.
- `Lemma26.lemma26-square : (n : Nat) -> is-pushout-square (Sq (suc n))` checks inside `Coh2`.
- Nothing is committed.
- The three candidate postulates are proved:
  - `IntervalPosetal.I-hom-contr`;
  - `SegalCoface.segal-coface-01/12`.
- Levels: the geometry is level 1 (Structure). Cones, products, TimesI, base-Sq1 and Lemma 26 are level 2. Nothing is level 3.

## Next: M6, Segal for all n (new; see DESIGN.md)

1. **Chains.** Define the type of chains of n composable morphisms of C, by recursion on n:
   - Chain 1 = Mor C;
   - Chain (n+1) = a chain glued to a morphism at the last vertex.
   Use the existing `Hom`, `dom`/`cod` and `ComposablePair` (SegalComparison) for n = 2.
2. **Restriction to the spine.** Define the map Map (Delta n) C -> Chain n, by the faces and last-edge (FaceMap, LastEdge, GluingSquare).
3. **Segal for all n.** Prove the restriction is an equivalence, by induction on n:
   - Lemma 26 says Delta (n+1) is the pushout of Delta n and Delta 1 over One;
   - Map (-, C) turns that pushout into a pullback of mapping types, and a cone of `Sq` is a chain glued at a vertex;
   - the base case is `segal-is-equiv` (n = 2) and `ob-map-equiv`/`I-char` (n = 0, 1).
   The comparison of `Sq (suc n)` at C is the step, so this layer is expected to sit in Coh2.
4. **Composition.** The fibres over a spine are contractible.
   - Composition is the centre at n = 2; compare it with `Segal.comp-hom`.
   - Associativity (n = 3) and the unit laws (degenerate simplices) are instances of contractibility.
   - Lock composition after these characterising lemmas.

## Then: M7, fully faithful functors

Results 33–39 of `~/AGDA/axioms.pdf`; Agda `Simplices/FullyFaithful.agda` (352 lines); `~/AGDA/HANDOFF-fullyfaithful-coherence.md` Step A.
- **Proved from M6:** `Hom-map-comp` and `id-hom-is-inv`. They are postulates in the Agda.
- **New parameters:** `rezk` and `I-detects-equiv` (Axiom 38), added to Structure.
- **Remark 39** comes last.

Redo the levels table after M7.

## Stop conditions

As in HANDOFF.md. In particular, ask before adding `Coh3`.

## Unit pitfalls met in M0–M5

- **Inference.** Hidden arguments are not inferred through definitions such as `Ob` and `Mor`, so give them as `{e}`.
  - A complex argument can also block inference. Name it with a typed `where` local instead.
- **`where` blocks.** No module aliases inside `where`. Locals must come before their uses.
- **Names.**
  - A file module and a record cannot share a name (this is why the file is `Squares` for the record `Square`).
  - No primes and no `!` in identifiers.
  - The earlier `open` wins, so for example write `SquareAlg.cone-eq` when `Pullbacks.cone-eq` is also open.
- **Grepping errors.** Grep for `ERROR\|FAILED`, not `rror`: SCOPE ERROR lines would be missed.
- **Paths.** `Prelude.trans` is J on the second path. Keep 2-cell chains right-nested and use `PathMoves` (`move2`/`move3`/`unmove3`/`nat-flip`/`pent-head`/`pent-mid`/`pent-sym`/`apt`/`apt7`/`tail7`).
- **Parallel work.** Each worker gets its own root file `AllX.seg` (a copy of All.seg plus its lines), checked with `seg AllX.seg --opened`, and never edits shared files. The parent merges.
