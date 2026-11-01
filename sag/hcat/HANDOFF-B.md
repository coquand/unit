# HANDOFF B: homology groups, Mayer–Vietoris, H_*(Sⁿ) (segment Homology)

Read first: `DESIGN-HOMOLOGY.md` (plan and status), `README.txt` (files), `HANDOFF.md` (working
rules), and the note `unit/doc/hcat-homology.pdf`.

## State (2026-11-01)

The segment `Homology` sits inside `Coh2` in `All.seg`. Its parameters are: `level k ;
constraint k < l`, `D : Cat`, `tensor`, `eta`, `tensor-up`. The following are done:
- H1–H2: functoriality, homotopy invariance, dimension, initiality of 0⊗A, additivity,
  Fubini;
- H3 excision: `Excision.ExcisionOf.excision`, in the sub-segment `WithPentagon`, whose only
  parameter is `hpent`, the pentagon of D.

The check: 103 modules, 0 failed, about 8 s. Nothing is committed.

## Task B (the user's choice)

Keep `hpent` as an explicit assumption; do not work on discharging it. Develop homology
itself:

1. **Pointed and stable D.** Add, as parameters of a new sub-segment inside `WithPentagon`
   (the excision results are needed):
   - a zero object;
   - pushouts in D, at least those of the form 0 ← A → 0, giving the suspension ΣA;
   - stability: a pushout square in D is a pullback, or the weaker and simpler requirement
     that Σ is an equivalence of D.

   Choose the weakest form that gives the long exact sequence, and record the choice in
   `DESIGN-HOMOLOGY.md`.
2. **Groups.** Define H_n(X;A) = ‖Hom(Σⁿ𝟙, X⊗A)‖₀ (or π_n of Hom(𝟙, X⊗A) at 0) for a unit
   object 𝟙 (a parameter). Then:
   - prove the group structure, from Hom(ΣB, E) ≃ Ω Hom(B, E), which follows from the
     universal property of the pushout 0 ← B → 0;
   - prove commutativity for n ≥ 2 (Eckmann–Hilton), or for all n using stability.
3. **The Mayer–Vietoris sequence.** Excision gives a pushout square in D. With stability
   that square is a fibre/cofibre sequence. Derive the long exact sequence of the groups,
   or at least exactness at the middle term and the connecting map.
4. **Suspension and spheres.** Take ΣX and Sⁿ as pushouts of types, given by their
   universal property (no HITs: a parameter "a pushout of 1 ← X → 1 exists", in the style
   of `TypePushout`). Prove H̃_{n+1}(ΣX;A) ≅ H̃_n(X;A) from excision. Derive H̃_*(Sⁿ) from
   the dimension axiom.

Write reduced homology as the cofibre of tmap of X → 1, or for pointed X as the cofibre of
1⊗A → X⊗A.

## Rules (unchanged)

- Follow `seg/WRITING.md`: informal proof in the file comment, one name per notion, lock
  after the characterising lemmas, `--opened`.
- Every shell command under 60 s (`timeout 55`). Every file under 1 s.
- Check with `./segc sag/hcat changed` from `unit/`, and stop the server at the end.
- No commits. No new axioms beyond named segment parameters. In reports, list the
  parameters and say "no new axioms", never "no axioms".
- Name J motives as definitions. Inline motives using `ccl`/`transH` gave "hidden argument
  found but cannot be written". `idJ` needs all six arguments. `ccl` inside motives needs
  `{f} {f1}`.
- Use `hcomp-assoc`, `AssocNat` and `DPushout` as they are. `hcomp-assoc` is not locked,
  and it opens far.
- Stop and ask:
  - if a step seems to need a coherence beyond `hpent` and level 2;
  - if a design choice in `DESIGN-HOMOLOGY.md` turns out wrong;
  - when 1–4 are done, after updating `DESIGN-HOMOLOGY.md`, `README.txt` and the note
    `unit/doc/hcat-homology.tex`, which carries a stamp and is concise.
