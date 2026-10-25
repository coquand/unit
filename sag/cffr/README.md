# cffr/: Coquand–Quitté, *Constructive finite free resolutions* (cffr.pdf)

Worker A's files; worker B's are in `../koszul/` (linked read-only here).
Check: `./segc sag/cffr all` from the `unit` root (cold: 209 modules, 0 failed, about 5.6 s).
Ring `Rg : Ring[l].CRing` with `setR`, or `D : TrueGrade.RD`; matrices by their
columns (`Matrices`); minors as exterior coordinates (`Minors`).

| cffr | statement | declaration |
|---|---|---|
| Lemma 2.1, Cor. 2.2 | regularity of products and powers | `RegularIdeal.Over.lemma21`, `corollary22` |
| Lemma 2.3 | local–global principle for regularity | `LocalRegular`, `LocalRegularMod` (mod J) |
| Thm 2.4 | injective ⇒ stable of rank p (McCoy) | `Minors.theorem24` |
| remark after 2.4 | injective R^(q+1+m) → R^q ⇒ 1 = 0 | `Minors.trivial` |
| Thm 2.5 | D_p regular ⇒ injective | `Minors.theorem25` |
| Thm 2.6, Cor. 2.7 | Vasconcelos | `koszul/Vasconcelos` (worker B) |
| Thm 3.1 | McCoy for polynomials (ctete Thm 4) | `PolyMcCoy.mccoy`, `converse`; `PolyRegular`, `PolyRegularMod` |
| Lemma 4.3 | ranks along an exact pair | `Lemma43.Over.lemma43` |
| §4.1–§6.7 | Koszul complex, grades, true grade, Lemma 6.7 | `koszul/` (worker B) |
| Thm 6.8 | ranks and grades along a resolution | `Thm68.theorem68` (with `Resolution`, `TopGrade`) |
| Thms 7.1–7.3, Cor. 7.4 | | `koszul/Resolutions`, `PeskineSzpiro` (worker B) |
| Cor. 7.5 | exactness criterion | `Cor75Inst.cor75` |
| Cor. 7.6 | Gr(D_n(A)) ≥ 3 ⇒ 1 ∈ D_n(A) | `Cor76.cor76` |
| Lemma 8.1 | v ⊥ u_i ⇒ u_1…u_p ⊥ v∧β | `Lemma81.Over.lemma81` (`killed`) |
| Lemma 8.2 | ω and β* proportional | `Lemma82.Over.L82.lemma82` (`Killed82`, `Exchange`) |
| Prop. 8.3 | Plücker–Sylvester | `ExteriorPluckerSylvester.At.cramer` (exterior/, frozen), used in `Lemma82.Exchange` |
| Lemma 8.4 | ∧^q(B) = γ β*^T, D_q(B) ⊆ (γ) | `Lemma84.Over.At.lemma84`, `minor-value`, `GammaGrade` |
| Cor. 8.5 | the β_i along (*) | `Cor85.Over.Chain.Res` (`stage`, `final`) |
| Lemma 8.6 | g with a = g b, Gr(b) ≥ 2, is a regular gcd | `Lemma86.Over.Lemma86` |
| Thm 8.7 | the Cayley determinant is a gcd of D_(r_1)(A_1) | `Thm87.Over.Thm87.Res.theorem87`, `det-regular` |
| Cor. 8.8 | Hilbert–Burch | `Cor88.Over.Cor88.cor88`, `gcd-regular` |
| Thm 8.9 | a resolution of R/(a) gives a regular gcd of the a_i (or a = 0) | `Thm89.Over.Thm89.theorem89` |
| Cor. 8.10 | two-generated ideals with resolutions ⇒ gcds | `Thm89.Over.Cor810.cor810` |

Tools for §8: `ColumnBlocks` (the matrix (y, v), sums over subsets),
`MinorTranspose` (minors of a rectangular transpose), `StarDual`
(star(y) = ±y*), `Lemma84.GrTwo` (Gr ≥ 2, explicit form; `Enlarge`),
`GradeBridge` (true grade ⇒ the explicit forms).

Deviations and gaps: see `../HANDOFF-CFFR-A.md` (section Gaps).  Wiebe's
theorem (ctete §2, step A7) is in `../wiebe/`.
