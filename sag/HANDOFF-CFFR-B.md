# Worker B: complexes, the Koszul complex and grade (cffr.pdf)

Read first: `sag/CFFR-DESIGN.md` (scope, split, representation choices,
rules), `sag/CFFR-INTERFACE.md`, `cffr.pdf` §4, §5, §6, `ctete.pdf` §1, and
`/Users/coquand/CANONICITY/seg/WRITING.md`.  You own `sag/koszul/` only.
Worker A works in `sag/cffr/` at the same time.  The pcc2 terminal works in
`sag/exterior/`: read-only for you.  Do not commit; report to the
coordinator.

## Steps

- **B0. Skeleton.** `koszul/All.seg`: links to the foundation (`pn/`), to
  `cokernel7/` (modules, submodules, quotients, localisation), to
  `em/Snake` if you reuse it, and to the finished files of `exterior/`
  (`ExteriorCoordinates`, `ExteriorVectorContraction`).  Check:
  `./segc sag/koszul changed` from the `unit` root.
- **B1. Complexes of R-modules.** Cochain complexes, cohomology vanishing
  (Hⁱ = 0 as "every cocycle is a coboundary"), maps of complexes, short
  exact sequences of complexes and the long exact sequence in the
  vanishing form.  `em/Snake` does this for abelian groups: generalise or
  instantiate it (R-modules are abelian groups with a scalar action); do
  not write a second connecting map.
- **B2. §4.** Lemma 4.1 (exactness modulo an H-regular a), Cor. 4.2.
- **B3. §5, the Koszul complex** C(a; E): functions `Index n -> E`
  graded by |I|, d α = a ∧ α, built from the exterior product of
  `exterior/` (design §4), d ∘ d = 0 from a ∧ a = 0; functoriality in E and
  exactness of C(a; −) on exact sequences.  Lemma 6.1 (x ∈ (a) kills
  Hⁱ(a; E)) from `exterior/ExteriorVectorContraction.mixed`
  (c_b(a ∧ α) + a ∧ c_b(α) = (b·a) α), extended to E-coefficients.
- **B4. §6, grade.** Gr(a; E) ≥ k; the explicit forms for k = 1, 2, 3
  (paper §6, items 1–3); Lemmas 6.2, 6.3 (short exact sequences),
  Thm 6.4 (0 → Rⁿ → R^m → E → 0), Lemma 6.5 (x E-regular in a:
  Gr(a; E) ≥ k + 1 iff Gr(a; E/xE) ≥ k).
  **Announce Lemmas 6.2, 6.3 and Thm 6.4 in `CFFR-INTERFACE.md` as soon as
  they check: A needs them for §7.**
- **B5. The true grade (ctete §1).** Lemma 1, Cor. 2 (a regular modulo b
  iff b regular modulo a), Lemma 3, Def. 5 (true grade, design §4),
  Lemma 6, Lemma 7, Thm 8 (Gr(I) ≥ k + 1 iff I regular and Gr(I) ≥ k
  modulo a Kronecker polynomial of I), **Thm 9** (Gr(I) ≥ k + 1 and b any
  regular element of I give Gr(I) ≥ k modulo b), with A's McCoy
  (ctete Thm 4) linked.  Then cffr Prop. 6.6 and Lemma 6.7 with the true
  grade (their proofs in cffr already argue this way).  **Announce Thm 9
  and Lemma 6.7: A needs them for Thm 6.8 and Wiebe.**
- **B6. The comparison: report first.** cffr's Thm 6.8 and §7 combine the
  Koszul grade of B4 with Lemma 6.7.  Either prove that the true grade
  and the Koszul grade Gr(a; R) ≥ k agree (cffr, after Lemma 6.5:
  Lemma 6.5 and invariance of the Koszul grade under adding
  indeterminates), or restate the §6 lemmas A uses with the true grade.
  Write in `CFFR-DESIGN.md` §2 what each needs and an estimate, and wait
  for the user's decision.

Done when each step checks under `./segc sag/koszul changed`, every file
< 10 s, and `koszul/README.md` lists what is proved with cffr numbering.

## Progress

- B0 (2026-10-25): `koszul/All.seg` links the pn foundation, exterior/
  (up to `ExteriorCoordinates`, `ExteriorVectorContraction`), cokernel7/
  (`Alg73`, `RingBridge`, `Submodules`, `QuotientModule`, `Localisation*`)
  and em/`Snake` with its closure.  Cold run: 107 modules, 0 failed, 1.26 s.
- B1 (2026-10-25): `Complexes` (Complex, Map, SES, Cx.Bnd/Vanish/Upto,
  modules as em Ab), `VanishLES` (AtC.vanish via em/Snake.ker-im; at-a,
  exactness at H(A), a chase Snake lacks; lemma62, lemma63, lemma-zero).
- B2: `ExactModulo` (Lemma 4.1 as Lift + Step; Cor. 4.2 at-e, at-f).
- B3: `Coefficients` (f |-> f_E by matrices, compose/plus/scale/zero/ext),
  `Koszul` (C(a;E) graded by support, dd = 0), `KoszulHomotopy`
  (deg-contract, contract-deg0, Lemma 6.1 = WithE.kills), `KoszulExact`
  (functoriality in E, SES of modules -> SES of complexes; choice over
  Index n).
- B4: `Grade` (Gr, Lemmas 6.2, 6.3, MultZero, Lemma 6.5), `Products`
  (retracts, powers, assemble, choice over Fin), `Thm64` (both parts, with
  cffr/Matrices), `GradeOne` (item 1, with cffr/RegularIdeal.Regular and
  `action E`).  Announced in CFFR-INTERFACE.md.  Items 2, 3: not yet.
  koszul/ 127 modules, all < 0.15 s; max openings 359 (Coefficients.delta).
- Items 2, 3: `KoszulCone` (d by recursion on n), `KoszulVectors`,
  `KoszulVectors3`, `GradeTwo`, `GradeThree`.
- B5: `RelRegular` (ctete Lemma 1, Cor 2, Lemma 3 modulo any IdealPred),
  `TrueGrade` (sequence form of Def. 5, relative to a list J; new variables
  on top), `TrueGradeTools`, `TrueGradeIdeals`, `TrueGradeThm9` (Lemma 6,
  Lemma 7, Gr >= 1 iff regular, Thm 9), `TrueGradeBase` (base change via
  ext1 (ext p D) ~ ext p (ext1 D)), `TrueGradeIso`, `TrueGradeProduct`
  (Prop. 6.6, cons), `TrueGradeLocal` (S[X][1/x] ~ S[1/x][X]),
  `TrueGradeLemma67` (Lemma 6.7).  All announced in CFFR-INTERFACE.md.
- Cold run 2026-10-25: 157 modules, 0 failed, 2.36 s; every file < 0.2 s;
  1568 own declarations, max openings 484 (TrueGradeLocal.LocUnique.at-fraction).
- B6: report in CFFR-DESIGN.md §2; user decision (A1).  Done:
  `TrueKoszulQuot` (R/J, the exact sequence 0 -> R/J -c-> R/J -> R/(J,c)
  -> 0, Lemma 6.5 back), `TrueKoszulDescent` (exterior coefficients along a
  ring map, semilinear maps commute with d, descent along D -> D[X] via
  constants and ev0), `TrueKoszul` (true-koszul, Absolute.result).
  Cold run: 161 modules, 0 failed, 2.95 s; slowest file 0.34 s.
- B7/B8 (coordinator's request for all of cffr): `Resolutions` (Thm 7.1 with
  A's layout + elementwise k = 1 form, Thm 7.2, Cor 7.4), `PeskineSzpiro`
  (Thm 7.3), `TrueGradeLocUp` (tgr-loc).  Cold run: 179 modules, 0 failed,
  4.15 s; slowest file 0.56 s (Resolutions).
- B9 (user's request via coordinator): `Vasconcelos` = cffr Thm 2.6 and
  Cor 2.7, directly on the ranks of `Resolution.ranks` (no localisation):
  Char = 0 by Cramer (adj of the transpose), Char > 0 by star/complement
  coefficients, Char < 0 by `too-big`.  Cold: 182 modules, 0 failed, 4.32 s;
  max openings 309.
- Pending (coordinator, 2026-10-25): the coefficient lemma along a ring map
  exists in three copies (TrueKoszulDescent.ExtBase.B-coeff, A's
  LocalExact.coeff-B, McCoyMod.Map.coeff-B); A will move one generic
  version into cffr/ — then switch ExtBase to it.

## Openings

(record here declarations above 500 total openings, with the cause)

Also `Resolutions.Chain.Step.iota-sm-inc` 514 (Modules.Over.Module and
Submodules.Over.Module, two names of the module type, compared).
Four in `TrueKoszulDescent.Down`: `phi-sm-inc` 735, `psi-sm-inc` 693,
`phi-add-inc` 573, `psi-add-inc` 563.  Cause: each step of these
computations on representatives of D/J and D[X]/J crosses between the two
rings' module records (Modules.Over.ring, RingBridge.ring, Alg73.Reg.reg,
Extension.ring are opened 50-130 times each); written with calc and the
points in ring terms (in the regular modules' terms it was worse, 641-826).
A generic "semilinear map out of a quotient module" lemma would move this
cost into one place; not done.
Fixed: ring aliases (Step67.D1, Comm.SX: up to 15763
openings where terms written with different aliases met; rings now written
by their expressions), TrueGradeBase.theta-compat (844: suc step split out),
KoszulVectors.dvec1 (852: Fin reopened by inl/inr lambdas; inr-part), KoszulHomotopy.kills (914: every u.1 reopened the
record-built complex; split into vector-level kill-zero/kill-suc),
Thm64.lin-of (501: Pow reg p reduced to Fin p -> R repeatedly; linearity
stated on Vec).

## Gaps

(statements of the paper used without proof, omitted verifications,
citations replaced by proofs)

- Thm 6.4 (2): cffr shows H^0(a;R) = 0 separately (A injective, n > 0);
  here VanishLES.lemma-zero covers degree 0 uniformly, and m > 0 is not
  needed.
- Lemma 6.5 is proved as the iff only (not the short exact sequence of
  cohomology groups, which are never formed).
- ctete Def. 5 is stated in sequence form (regular sequence of length k
  after indeterminates); the recursive form is the pair Thm 9 / cons.
  ctete Thm 8 is not stated separately (Lemma 7 + cons are its two halves).
- Prop. 6.6 is proved for any list P containing the products I_i K_j
  (stronger than P = I K; no enumeration of products needed).
- cffr's "regular element both in I and J" (Prop 6.6) is c = f g with f, g
  Kronecker polynomials in two new variables.
- Rings: no quotient rings; "modulo J" is elementwise (coordinator).
