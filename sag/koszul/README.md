# koszul: complexes, the Koszul complex, grade and true grade

Worker B of the formalisation of T. Coquand, C. Quitté, *Constructive finite
free resolutions* (`cffr.pdf`), §4–§6, with the true grade of T. Coquand,
C. Tête, *An elementary proof of Wiebe's Theorem* (`ctete.pdf`), §1.
Design: `../CFFR-DESIGN.md`; interface: `../CFFR-INTERFACE.md`; log:
`../HANDOFF-CFFR-B.md`.  Check from the `unit` root: `./segc sag/koszul all`
(182 modules, about 4 s cold; every file under 0.6 s; five declarations
open 510–740 definitions, recorded in the handoff).

Rings are `Ring[l].CRing` with `setR`; modules are Alg73 modules over the
`RingBridge` ring (`Modules[l].Over[Rg,setR].Module`); a in R^N is
`a : Presentations.Fin N -> R`.  Linked read-only: the pn foundation,
`exterior/` (coordinates, degrees, contraction), `cokernel7/` (modules,
quotients, localisation), `em/Snake`, and from `cffr/` (worker A):
`Matrices`, `RegularIdeal`, `PolyMcCoy`, `PolyRegular`, `PolyIdeal`,
`PolyRegularMod`, `LocalRegular`, `LocalRegularMod`, `Flat`.

## Koszul grade (cffr §4–§6)

| cffr | statement | declaration |
|---|---|---|
| — | complexes of modules, maps, short exact sequences; H^k = 0 as "every cocycle is a coboundary" | `Complexes` (`Complex`, `Map`, `SES`, `Cx.Vanish`, `Cx.Upto`) |
| — | long exact sequence, vanishing form | `VanishLES.LES` (`AtC.vanish` by `em/Snake.ker-im`; `at-a`, `vanish-a`) |
| Lemma 4.1 | exact modulo an H-regular a | `ExactModulo.Lemma41.result` |
| Cor. 4.2 | short exact sequences stay exact modulo a G-regular a | `ExactModulo.Cor42.at-e`, `at-f` |
| §5.2 | C(a; E) = (Index n → E) graded by \|I\|, d α = a ∧ α, d d = 0 | `Coefficients` (f ↦ f_E), `Koszul.K.complex` |
| §5.2 | C(a; −) functorial, exact on short exact sequences | `KoszulExact.Fun`, `KoszulExact.Ses.ses` |
| Lemma 6.1 | x = b·a kills H^p(a; E) | `KoszulHomotopy.WithE.kills` (from `ExteriorVectorContraction.mixed`) |
| §6 | Gr(a; E) ≥ k | `Grade.Gr` |
| §6 item 1 | Gr ≥ 1 iff a regular for E | `GradeOne.Item1.forward`, `back` |
| §6 item 2 | Gr ≥ 2 iff Gr ≥ 1 and a_i y_j = a_j y_i ⇒ y = a e | `GradeTwo.Item2.forward`, `back` |
| §6 item 3 | Gr ≥ 3 iff Gr ≥ 2 and the three-term condition | `GradeThree.Item3.forward`, `back` |
| Lemma 6.2 | Gr(E) ≥ k+1, Gr(F) ≥ k ⇒ Gr(G) ≥ k | `Grade.SesGrade.lemma62` |
| Lemma 6.3 | Gr(F) ≥ k+1, Gr(G) ≥ k ⇒ Gr(E) ≥ k+1 | `Grade.SesGrade.lemma63` |
| Thm 6.4 | 0 → R^n → R^m → E → 0: Gr(a) ≥ k+1 ⇒ Gr(a; E) ≥ k, and the converse when n > 0 and A has coefficients in a | `Thm64.Thm64.part1`, `Thm64.Part2.part2` |
| Lemma 6.5 | x = b·a E-regular: Gr(a; E) ≥ k+1 iff Gr(a; E/xE) ≥ k | `Grade.Lemma65.forward`, `back` |

Supporting: `Products` (retracts, powers X^m), `KoszulCone` (d by
recursion on n), `KoszulVectors`, `KoszulVectors3` (the vectors of degree
0–3 used for the items).

## True grade (ctete §1; cffr Prop. 6.6, Lemma 6.7)

Everything is relative to a list J ("modulo J", elementwise; coordinator's
decision).  Indeterminates are adjoined on top: `ext (p+1) D = (ext p D)[X]`.

| source | statement | declaration |
|---|---|---|
| ctete Def. 5 | Gr(I) ≥ k mod J: merely a regular sequence of length k in I, after p indeterminates | `TrueGrade.TGr`, `RegSeq`, `mono` |
| ctete Lemma 1 | a, b regular, a y = b x: x ∈ (a) iff y ∈ (b) | `RelRegular.lemma1` (modulo any ideal) |
| ctete Cor. 2 | a regular mod b iff b regular mod a | `RelRegular.cor2` |
| ctete Lemma 3 | I regular mod a iff mod b | `RelRegular.lemma3` |
| ctete (after Def. 5) | Gr(I) ≥ 1 iff I regular | `TrueGradeThm9.gr1-to`, `gr1-from` |
| ctete Lemma 6 | Gr(I) ≥ 2, b regular ⇒ I regular mod b | `TrueGradeThm9.Lemma6.result` |
| ctete Lemma 7 | Kronecker f, a_1..a_k regular ⇒ f, a_1..a_{k−1} regular | `TrueGradeThm9.Lemma7.seq` |
| ctete (after Def. 5) | c ∈ I regular and Gr ≥ k mod c ⇒ Gr ≥ k+1 | `TrueGradeProduct.cons` |
| ctete Thm 9 | Gr(I) ≥ k+1, b regular in I ⇒ Gr(I) ≥ k mod b | `TrueGradeThm9.thm9` |
| ctete §1 remark | invariance under adding an indeterminate | `TrueGradeBase.base-change` |
| cffr Prop. 6.6 | Gr(I), Gr(K) ≥ k ⇒ Gr(P) ≥ k for any P ⊇ IK | `TrueGradeProduct.prop66` |
| cffr Lemma 6.7 | Gr(x) ≥ k and Gr(a) ≥ k over each R[1/x_i] ⇒ Gr(a) ≥ k | `TrueGradeLemma67.lemma67` |

Supporting: `TrueGradeTools` (towers, moving up along ext p),
`TrueGradeIdeals` (ideals of lists, (J, a), swap), `TrueGradeIso`
(invariance under ring isomorphisms; polynomial maps on Kronecker
polynomials), `TrueGradeLocal` (S[X][1/x] ≅ S[1/x][X]).

ctete Thm 8 is used in the form of Lemma 7 and `cons` (its two directions);
it is not stated separately.

## True grade gives Koszul grade (cffr after Lemma 6.5; step B6, option A1)

| statement | declaration |
|---|---|
| Gr(I) ≥ k mod J (true) ⇒ Gr(I; D/J) ≥ k (Koszul) | `TrueKoszul.true-koszul` |
| Gr(I) ≥ k (true) ⇒ Gr(I; D) ≥ k (Koszul) | `TrueKoszul.Absolute.result` |
| Lemma 6.5 (back), with D/(J, c) for c = v·a regular mod J | `TrueKoszulQuot.Lemma65J.back` |
| descent of the Koszul grade along D → D[X] (constants and ev₀) | `TrueKoszulDescent.Down.upto`, `down-p` |

The converse (Koszul ⇒ true, option A2) is not done: not needed by §7–§8.

## §2.2 Vasconcelos

| cffr | statement | declaration |
|---|---|---|
| Thm 2.6 | resolution of E: Char = 0 ⇒ Ann(E) regular; Char > 0 ⇒ Ann(E) = 0; Char < 0 ⇒ 1 = 0 | `Vasconcelos.Res.Thm26.char-zero`, `char-pos`, `char-neg` (matrix level: `Zero`, `Pos`, `neg-char`) |
| Cor 2.7 | (a) has a resolution ⇒ a = 0 or a regular | `Vasconcelos.Res.Cor27.result` (with `Cyclic` for E = R/(a)) |

## §7 (Koszul grade, modules) and localization of the true grade

| cffr | statement | declaration |
|---|---|---|
| Thm 7.1 | resolution of length K+1 of E, Gr(a) ≥ t+K+1 ⇒ Gr(a; E) ≥ t (A's matrix layout) | `Resolutions.Chain.thm71`; k = 1 elementwise: `Chain.Elem.result` |
| Thm 7.2 | p > 0, top matrix in (a), Gr(a; E) ≥ k ⇒ Gr(a) ≥ k+K+1 | `Resolutions.T72.thm72` |
| Thm 7.3 | Peskine–Szpiro | `PeskineSzpiro.PS.exact` |
| Cor 7.4 | Rees | `Resolutions.Chain.rees` |
| (for Cor 7.5) | Gr(I) ≥ k mod J over D ⇒ over D[1/x] | `TrueGradeLocUp.tgr-loc` |
