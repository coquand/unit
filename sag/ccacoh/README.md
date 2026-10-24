# ccacoh: cohomology in synthetic Stone duality (CCA §3.1–3.3)

Worker B of the CCA formalisation (`../CCA-DESIGN.md`, `../HANDOFF-CCA-B.md`).
Uses SSD (`../stone`, `../stoneseq`), worker A's `../cca` (Props 2.3.5,
2.3.7, Lemma 2.1.7, local choice) and `../em` (non-abelian torsors and
Čech cohomology, plain HoTT), all by links.  Check with
`./segc sag/ccacoh changed` from the `unit` root.

## Proved (CCA numbering)

| CCA | statement | file, declaration |
|---|---|---|
| Def. 3.1.1, 3.1.2 | non-abelian cocycles, Ȟ¹ = 0, H¹ = 0 (left torsors, CCA's formulas mirrored) | `em/CechNA`: `CechNA.H1Zero`, `CohZero` |
| Lemma 3.1.3 | a point of a torsor is a trivialisation, and back | `em/GTorsor`: `GTor.pt-triv`, `triv-pt` |
| Lemma A.0.1, A.0.2 (i), A.0.4 (i), (ii) | | `em/CechNA`: `lemmaA01`, `Points.phi`, `Points.cocycle`, `Psi.tor`, `Psi.H` |
| Lemma A.0.6, Cor. A.0.8 | vanishing form | `em/CechNA`: `Points.trivialise`, `CorA08.forward`, `backward` |
| Lemma 3.1.5 | in the form used: for the tower of Lemma 2.1.7, cochains of pairs and triples are the colimits of the stage cochains (Props 2.3.5, 2.3.7) | `ScottCech.Over.Stages.phi2-equiv`, `phi3-equiv` |
| Lemma 3.1.6 | Ȟ¹(S, T, G) = 0 for S, T x Stone, G x overtly discrete | `H1Stone.Over.lemma316` |
| Prop. 3.1.7 | H¹(S, G) = 0 for S Stone | `H1Stone.Over.prop317` |
| Prop. 3.1.8 | vanishing form: H¹(X, G) = 0 iff Ȟ¹(X, S, G) = 0 for S ->> X, S Stone | `H1Stone.Over.Prop318.forward`, `backward` |
| Prop. 3.1.8 | as a bijection of sets: Ȟ¹(X, S, G) ≃ H¹(X, G) (X any type) | `Prop318Set.Over.prop318` |
| Prop. 3.1.4, Cor. A.0.7, A.0.8, Lemmas A.0.2 (ii), A.0.4 (iii), A.0.5, A.0.6 | as bijections of sets (plain HoTT) | `em/CorA07`: `CorA07.corA07`, `A08.corA08` |
| Def. 3.2.1, Lemmas 3.2.2–3.2.4 | ε by delooping (plain HoTT) | `em/Eps` |
| Thm 3.2.5 | ε : K(Π A, m) → Π K(A x, m) is an equivalence (S Stone, A x overtly discrete) | `Thm325.Over.thm325` |
| Cor. 3.2.6 | Hᵐ(S, A) = 0 for m ≥ 1 | `Thm325.Over.cor326` |
| Def. B.0.3 | S ->> X is a Čech cover (X compact Hausdorff, S Stone) | `Thm332.Over.Cov.conn` |
| Lemma B.0.4 | H-side, vanishing form: exactness Hⁿ(X, L) -> Hⁿ⁺¹(X, A) -> Hⁿ⁺¹(X, A^S) | `em/Exact` with `Thm332.Over.Step` |
| Thm 3.3.2 | form (C) (`../CCA-DESIGN.md` §5): if Ȟ¹(X, S, B) = 0 for all overtly discrete B, then Hⁿ(X, A) = 0 for all n >= 1 | `Thm332.Over.thm332` |
| Def. 3.3.1 | higher Čech complexes, vanishing form | worker A's `cca/Cochains`: `Cech.Vanish` |
| — | Čech dimension shift: Ȟ^(m+2)(X, S, B) = 0 gives Ȟ^(m+1)(X, S, B^S / B) = 0 (cone; lifting over the Stone (x : X) * S(x)^(k+1); chase) | `em/CechHigher`: `Shift.vanishS`, `Shift.shift`; `LiftStone`; `Thm332C.Over.lifts`, `w-stone` |
| Thm 3.3.2 | form (C') (`../CCA-DESIGN.md` §5): if Ȟ^(m+1)(X, S, A) = 0 for all m, then Hⁿ(X, A) = 0 for all n >= 1 | `Thm332C.Over.thm332` |

The long exact sequence used in Thm 3.2.5 is the fibre sequence
`em/FibSeq` and its exactness `em/Exact`; the cokernel L = A^T/A is the
image of the Čech differential (`em/ImageGroup`), overtly discrete by SSD
Lemma 2.7 and Prop. 2.3.9 (`Thm325.Over.odiscL`).

Not formalised (user's decision, `../CCA-DESIGN.md` §5): Appendix B on the
Čech side (Lemmas B.0.1, B.0.2, B.0.5, B.0.6, the missing B.0.7), Thm 3.3.2
as a natural group isomorphism.  The degree-1 comparison is done as a
bijection of sets (`Prop318Set`), without the group structures.
