# Worker A: regularity, McCoy, finite free resolutions, Cayley determinants (cffr.pdf)

Read first: `sag/CFFR-DESIGN.md` (scope, split, representation choices,
rules), `sag/CFFR-INTERFACE.md`, `cffr.pdf` §2, §3, §4 (Lemma 4.3), §6
(Thm 6.8), §7, §8, `ctete.pdf` §1 (Thm 4) and §2 (Wiebe's theorem), and `/Users/coquand/CANONICITY/seg/WRITING.md`.  You own
`sag/cffr/` only.  Worker B works in `sag/koszul/` at the same time.  The
pcc2 terminal works in `sag/exterior/`: read-only for you.  Do not commit;
report to the coordinator.

## Steps

- **A0. Skeleton.** `cffr/All.seg` like `exterior/All.seg`: links to the
  foundation (`pn/`), to the finished files of `exterior/` (determinants,
  coordinates, duality), to `cokernel7/` (modules, localisation) and
  `horrocks/LocalGlobal`.  Check: `./segc sag/cffr changed` from the `unit`
  root.
- **A1. §2.**
  - Regular elements and regular finitely generated ideals, for R and for
    a module E; Lemma 2.1, Cor. 2.2.
  - **Lemma 2.3** (the local–global principle replacing minimal primes):
    state it once, generally, in a file of its own; B needs it.
  - Minors as exterior coordinates (design §4); 𝒟_k(A); "stable of rank
    p"; Thm 2.4 (McCoy: injective ⇒ stable of rank p, by induction with
    Lemma 2.3 and the normal form diag(1, B) over R[1/aᵢ]), the remark
    after it (injective Rᵖ → R^q with p > q ⇒ R trivial), Thm 2.5.
  - Finite free resolutions, Char_R(E), Thm 2.6 (Vasconcelos), Cor. 2.7.
  - **Announce Lemma 2.3, regularity and 𝒟_k in `CFFR-INTERFACE.md` as soon
    as they check.**
- **A2. McCoy for polynomials: ctete Thm 4 = cffr Thm 3.1** (c(f) is
  regular iff f is regular in R[u₁, …, u_p]; both directions).  Prove it
  for one indeterminate (ctete's induction on the leading coefficients)
  and iterate; regularity of an ideal is invariant under R → R[u].  Check
  what `horrocks/`, `polynomial/` and `pn/` already have (regularity of
  monics, coefficients, PolynomialRing); reuse.  **Announce it: B needs it
  for the true grade.**
- **A3. Lemma 4.3** (exact Rᵖ → R^q → Rˡ with A stable of rank n ⇒ B
  stable of rank q − n), by Lemma 2.3 and Thm 2.4.
- **A4. After B's Lemmas 6.2, 6.3, Thm 6.4 are stable:** §7: Thm 7.1
  (Auslander–Buchsbaum–Hochster, one half), Thm 7.2 (the other, a new
  formulation), Thm 7.3 (Peskine–Szpiro), Cor. 7.4 (Rees), Cor. 7.5
  (exactness criterion), Cor. 7.6.
- **A5. After B's Lemma 6.7:** Thm 6.8 (exact finite free complexes:
  ranks rₖ, Aₖ stable of rank rₖ, Gr(𝒟_{rₖ}(Aₖ)) ≥ k).
- **A6. §8.** Lemma 8.1 (with B's interior product, i.e. exterior
  `contract`), Lemma 8.2 (new formulation), Prop. 8.3 **linked from the
  pcc2 terminal's Theorem 1, not reproved**, Lemma 8.4, Cor. 8.5 (new),
  Lemma 8.6, Thm 8.7 (the Cayley determinant is a gcd), Cor. 8.8
  (Hilbert–Burch), Thm 8.9, Cor. 8.10.
- **A7. Wiebe's theorem** (ctete Thm 11, Cor. 12): if (b) = (a)V with
  det V = Δ and Gr(b) ≥ n (B's true grade), then in R/(b),
  Δ⊥ = (a) and (a)⊥ = (Δ).  Induction on n with ctete Thm 9 (from B) and
  Cramer's rule (from the pcc2 terminal's `exterior/` files, linked).
  ctete §3 (automatic proofs) is out of scope.

Done when each step checks under `./segc sag/cffr changed`, every file
< 10 s, and `cffr/README.md` lists what is proved with cffr numbering.

## Progress

- 2026-10-25 A0: `cffr/All.seg`, symlinks to the real files (84 linked
  modules).  Linked from exterior/: the frozen files plus Coordinates,
  Duality, VectorContraction (unstable; see CFFR-INTERFACE).
- 2026-10-25 A1 (part): `RegularIdeal` (Lemma 2.1, Cor. 2.2),
  `LocalRegular` (Lemma 2.3 + R[1/a]), `Matrices`, `BaseChange`,
  `WedgeStep`, `Flat`, `McCoy`, `Minors` (D_k, stable, Thm 2.4, remark,
  Thm 2.5).  Announced.  All files < 0.15 s, max 205 openings.
  Representation: D_k(u) is indexed by k-tuples of columns (not k-subsets),
  which generates the same ideal (repeated columns give 0, permutations a
  sign) and needs no cardinality.  Thm 2.4 is proved with q fixed: in
  R[1/v_i] the other columns are sheared to be orthogonal to e_i, and
  contraction by e_i removes the last factor (WedgeStep).

- 2026-10-25 A2: `PolyMcCoy` (raw, family form: induction on the length of g,
  running through the tails of each f_j), `PolyRegular` (in the quotient
  ring R[X]; ideal invariance under R -> R[X]; Kronecker polynomial).
  Announced.  Multi-variable Thm 3.1 is by iteration of one variable (no
  monomial orderings), as the design asks.

- 2026-10-25 (B's request, option R): RegularIdeal now has a zero predicate
  (`Action.Z`), `IdealPred`, `IdealLaws`, `zero-ideal`, `modulo`,
  `Generated`; PolyMcCoy modulo an ideal; `PolyIdeal` (J.R[X] coefficientwise);
  `ev0`.  `MinorKill` (x kills D_k(u) => x kills all k-wedges of im u).
- A3 plan (Lemma 4.3), induction on n with q fixed, all rings, l varies:
  P(n): BA = 0, ker B in im A, D_{n+1}(A) = 0, D_n(A) regular, q = n + r
  => D_{r+1}(B) = 0, D_r(B) regular.  n = 0: A = 0, B injective, Thm 2.4.
  n+1: entries of A regular (enumerate Fin p x Fin q), Lemma 2.3 at the
  entries; in L = R[1/a_ij], a = a_j, lambda = a_ij^{-1} e_i, pi = 1 - a lambda,
  A' = pi A (rank n), B' = (B ; lambda) : R^q -> L^{l+1}; (A', B') exact.
  One core lemma (Split): if lambda(a) = 1, V = im M in ker lambda and x
  kills all m-wedges of V, then x kills all (m+1)-wedges of V + L a
  (contract-right, shear with a suffix Y such that g Y = 0).  It gives
  D_n(A') regular from D_{n+1}(A) regular and D_{r+1}(B') <- D_r(B); the
  other relations are WedgeStep.cancel and the computation of the last
  coordinate of B'.  Also needed: exactness and regularity transported to
  R[1/c].

- 2026-10-25 later: `PolyRegularMod` (B's (1)-(3)), `CommonPower`,
  `Splitting` (the core lemma of the A3 plan) check.  Cold run
  `./segc sag/cffr all`: 103 modules, 0 failed, 1.39 s; every cffr file
  < 0.12 s; no declaration above 460 openings (max MinorKill.Image.step 459).
  Next: LocalExact (exactness and regularity of D_k carried to R[1/c], using
  CommonPower), enumeration of Fin p x Fin q, Lemma43; then Thm 2.6.

- 2026-10-25: **A3 done**: Lemma 4.3 (`Lemma43.Over[p,q].lemma43`, image
  form).  Files: `LocalExact` (R[1/c]: regularity of a family with common
  exponents, exactness, B A = 0, coefficients), `FinPairs` (enumeration of
  Fin p x Fin q), `MinorForms` (minor form <-> image form, and to R[1/c]),
  `ExtraRow` (B' = (B ; lambda): down and up), `UnitStep` (A', B' when an
  entry is a unit), `Lemma43`.  `WedgeStep` gained `vdot-sum` (a copy of
  ExteriorTranspose.vdot-sum, which is not linked while pcc2 edits it) and
  `vdot-apply`.

- 2026-10-25 for B's Lemma 6.7: `LocalRegularMod` (Lemma 2.3 modulo J, with
  the R[1/a_i] instance) and `Enumerate` (D_k(u) as a list `minor-list`).
  Announced.  The commutation R[u][1/x] ~ R[1/x][u] is B's.
- 2026-10-25 A5 (Thm 6.8) in progress.  User chose (A1) for B (done by B:
  TrueKoszul).  cffr/All.seg now follows koszul/All.seg's order (B's files
  link some cffr files) and links B's true-grade files read-only.
  Checked: `Resolution.ranks` (ranks along a resolution: 1 = 0 or
  ranks s_k with A_k stable of rank s_k, by Thm 2.4 and Lemma 4.3);
  `QuotientRing` (R/I, internal only); `McCoyMod.mccoy-mod` (Thm 2.4 mod I,
  via R/I); `ExactMod` (Lemma 4.1 mod (J, b): inj-step, exact-step);
  `PolyExact` (injective/exact mod J carried to R[X] mod J[X]);
  `TopGrade.top-grade` (Gr(D_(p_m)(A_m)) >= m mod J, true grade).
  Remaining for Thm 6.8 (lower maps, Gr(D_(r_i)(A_i)) >= i): induction on
  (m, p_m) with Lemma 6.7 at the entries x of A_m (Gr(x) >= m since the
  minors lie in (x)); in R[1/x] (x = a_ij a unit) the reduced resolution
  A_m with column j removed (still injective), B' = (A_(m-1) ; lambda),
  (A_(m-2) | 0), A_(m-3), ...; needs membership versions of MinorKill.image
  and Splitting (coefficients in an ideal instead of killed by x), column
  deletion, TGr monotone under inclusion of ideals.
- 2026-10-25 **A5 done: Thm 6.8** (`Thm68.theorem68`), top-down layout.
  Grades by induction on k and the top size p: p = 0 shifts the complex;
  p = p0+1 uses Lemma 6.7 (B) at the entries of u and, in R[1/x], the
  reduced resolution of `Reduce` (u minus a column, (T0;lambda), (T1|0));
  `Resolution` rewritten top-down.  New: `IdealExt`, `GradeTools`,
  `Reduce`, `Thm68`; `Splitting`, `MinorKill.Image`, `ExtraRow.UpIn` made
  ideal-generic.  Cold run 181 modules, 0 failed, 3.17 s; no declaration
  above 320 openings in these files.
- 2026-10-25 **Cor 7.6 done** (`Euler`, `Cor76`): D_n(A) stated as the
  coefficients of the wedge of A's columns (c = identity), which avoids a
  permutation lemma; Cor 7.5 needs only D_n(A) inside the all-c list.
  Cold run: 191 modules, 0 failed, 4.02 s.  §7 complete.  Next: Thm 2.6
  (Vasconcelos) + Cor 2.7, then §8 (Prop 8.3 from ExteriorPluckerSylvester).
- 2026-10-25 **Cor 7.5 done** (`Cor75`, `Cor75Inst`, `LocalExactness`,
  `Reduce.Back`/`Down`).  Next Cor 7.6: Delta(v) = top(W i(v)), W the wedge
  of A's n columns in Lambda(R^(n+1)); Delta A = 0 (repeated factor);
  identity sum_k c_k(W e_k) = alpha(W) for W a product of n generators
  (E(P) = sum_k c_k(P) e_k = -m alpha(P)), giving D_n(A) = (Delta) both
  ways; exactness by Cor 7.5, then B's Rees (Chain.rees) on R/(Delta).
- 2026-10-25: Thm 2.6 + Cor 2.7 REASSIGNED to worker B (task B9, koszul/),
  at the user's request; A takes §8 (Prop 8.3 from the frozen
  ExteriorPluckerSylvester.At.cramer).  exterior/ frozen (EXTERIOR-FROZEN.sha256).
- Thm 2.6 (Vasconcelos), plan: (a) ranks along a resolution by Thm 2.4 at
  F_m and Lemma 4.3 downwards: A_1 is stable of rank r_1 = p_1 - p_2 + ...,
  so Char = p_0 - r_1 (this is also the first half of Thm 6.8); (b) Char < 0:
  r_1 > p_0, the r_1-wedges in Lambda(R^p0) vanish and are regular: 1 = 0
  (as Minors.trivial); (c) Char = 0: each p_0 x p_0 minor d of A_1 is in
  Ann(E) by Cramer (d y in im A_1; prove the relation sum_k +-det(v without
  k) v_k = 0 for n+1 vectors of R^n by contracting their wedge, which is 0);
  so Ann(E) contains the regular D_p0(A_1); (d) Char > 0: a in Ann(E) gives
  a.(W e_j) = 0 for W an r_1-wedge of im A_1; the coefficient of W e_j at
  I + {j}, j not in I, is +-coeff_I(W) (needs supports of homogeneous
  elements, ExteriorHomogeneous, or Lemma 2.3 at the r_1-minors).
  Not started; the paper's own route (split off a unit, lowering p_m and
  p_(m-1)) needs deleting a coordinate of Fin (q+1).

## Start here for §8 (fresh session, 2026-10-25)

State: §2-§7 done (A + B), cffr cold 196 modules, 0 failed, 4.82 s.
exterior/ FROZEN (EXTERIOR-FROZEN.sha256); B is on Thm 2.6/Cor 2.7 (B9).
§8 scope: Lemmas 8.1, 8.2, Prop 8.3, Lemma 8.4, Cor 8.5, Lemma 8.6, Thm 8.7,
Cor 8.8, Thm 8.9, Cor 8.10 (see CFFR-DESIGN.md §2 and the B6 assessment:
§8 needs true => Koszul only, Gr(beta) >= 2).
Prop 8.3 = `ExteriorPluckerSylvester[l].Over[Rg,setR].At[n,p,a,B].cramer`
(`.plucker-sylvester` = contraction form), already linked in cffr/All.seg.
Tools: Thm68 (true grades + ranks), Cor75Inst.cor75 (exactness criterion),
Cor76 (Delta, D_n(A) = (Delta)), Euler (exterior sums, E/S identities),
Minors/MinorKill/IdealExt (coefficient ideals), Reduce (unit-entry
reduction), LocalExactness.glue.  Read cffr.pdf §8 first (pdftotext into the
scratchpad), write the informal plan in a file header, then formalise.
Coordinator duties: B reports to this session (canonicity-69).

- 2026-10-25 §8 started: **Lemma 8.1** (`Lemma81`), **Lemma 8.2** (`Lemma82`,
  with `ColumnBlocks`); Prop. 8.3 is `ExteriorPluckerSylvester.At.cramer`
  (used by Lemma82.Exchange, not reproved).  Lemma 8.2 is proved for any w
  of degree p killed by the v_l (Killed82), with n = plus q p and
  "proportional" over all subsets (equivalent for degree p).  Cramer is
  applied to B = (y, v): the subsets meeting the v positions give products
  with a v factor (orthogonal to w), the only remaining subset of size p is
  the first block.  Files 0.04-0.15 s; max openings 400
  (ColumnBlocks.Blocks.replace-lift: plus/lift in the recursive types).
  B9 (koszul/Vasconcelos) linked.  Cold run: 200 modules, 0 failed, 4.56 s.
- 2026-10-25 **Lemma 8.4, Cor 8.5, Lemma 8.6, Thm 8.7 done.**
  `MinorTranspose` (rectangular Lambda(u), contraction naturality,
  transpose-pair, minor-transpose: coeff_L(u_K) = coeff_K((u^T)_L)),
  `StarDual` (y x = alpha^q(x) y; star(y) = (sgn p)^q y* for y a product of
  q generators), `Lemma84` (with `GrTwo` = Gr >= 2 in explicit form, gamma
  by unique choice, `GammaGrade`: Gr(D_q(B)) >= 2 => Gr(gamma) >= 2,
  `gamma-regular`), `Cor85` (Stage/base/Step; Chain[s,e0].Res[T,M,...]:
  top-down indexing, F_(t+1) = R^(rk(t+1) + rk t), M 0 = the map into the
  top module, beta_(m+1) = 1), `Lemma86` (Gcd, Divides, RegularElement),
  `Thm87` (StarGrade, OmegaGrade, Thm87[s,e0,T,ez].Res.theorem87 with
  ez : s (T+1) = 0 so F_0 = R^(r_1); det = [beta_1]).
  Deviation: the dual element in Lemma 8.4 is unstar(beta), = +-beta*
  (sign depends only on p, q, absorbed in gamma).  D_k is indexed by
  subsets (Lemma84.MinorX: K of size q, J any), not by tuples as in Minors.
  Cold run 206 modules, 0 failed, 5.12 s; max openings 402
  (MinorTranspose.vdot-transpose: Matrices.Vec vs Alternating.Vec, two
  names for Fin n -> R).
- 2026-10-25 **§8 complete: Cor 8.8, Thm 8.9, Cor 8.10.**  §8 now uses
  the tuple minors of `Minors` (as Thm 6.8 does): Lemma84.minor-value
  (B_c = h_c gamma, h_c = (e_c | bhat)), `Enlarge` (Gr >= 2 survives
  adding elements to a family), Cor85 with dimensions as data
  (rk (t+1) + rk t = d (t+1), so Thm68's layout fits), `GradeBridge`
  (true grade => regular / GrTwo, through TrueKoszul.Absolute and
  GradeOne/GradeTwo), `Lemma86.Transfer`, `Cor88` (Hilbert-Burch, with
  `OneRow`), `Thm89` (Theorem 8.9, Corollary 8.10).  Thm 8.9 uses Thm 6.8's
  stable ranks for the last map (rank 0: a = 0; rank >= 2: 1 = 0; rank 1:
  Thm 8.7) instead of Vasconcelos.  `cffr/README.md` lists cffr numbering.
  Cold run 209 modules, 0 failed, 5.56 s.
- Next: Wiebe's theorem (A7), not started.

## Openings

(record here declarations above 500 total openings, with the cause)

- `Cor75Inst.Inst.thm71`: 692 (0.01 s).  Cause: two instances of B's
  `Resolutions.Over.Chain[K,...].Elem` (K = 0 and K = suc k); each opens the
  Chain module's types (pdim/pmap, Coker, the quotient).  The fibre
  conversions are already factored (to-pt/from-pt; 873 before).

- `Lemma43.Over.Next.regular-minors`: 573 (0.01 s; 625 before the `Lr`
  aliases of Flat/LocalExact were removed).  Remaining cause: the hypothesis
  of Lemma 2.3 (`LocalRegular.Ideal`) is stated with
  `RegularIdeal.Over[L i, self (L i)]` and is met by
  `Minors.Over[I.ring,setL].RegularD`; the two Kills are compared by
  unfolding `self`/`modulo` (23 each) and the fraction carrier
  (`MonoidFractions.Fraction` 46).  Acceptable; a statement of Lemma 2.3
  over a given Action would avoid it.

- `GradeBridge.Over.Bridge.Two.result`: 1702, `Bridge.regular`: 1612
  (0.01 s).  Cause: B's Koszul grade is for the module R0 =
  `Modules.regular` built through `RingBridge`; identifying regularity /
  the explicit Gr >= 2 condition for R0 with those in R unfolds the bridge
  (Modules.ring, RingBridge.ring, Alg73.Reg.reg about 300 times each).  A
  refl lemma for the identification costs the same (tried, reverted).  A
  statement of GradeOne/GradeTwo items for R itself would avoid it.

## Gaps

(statements of the paper used without proof, omitted verifications,
citations replaced by proofs)

- cffr Thm 3.1 for several indeterminates and arbitrary distinct monomials:
  proved for one indeterminate (family form, modulo an ideal); several
  indeterminates by iterating R[u][v] = (R[u])[v].  The monomial-ordering
  proof of ctete Thm 4 is replaced by induction on the length of g.
- D_k(u) is generated by coefficients of products of k chosen columns
  (tuples); it is the ideal of k x k minors, but the comparison with
  submatrix determinants is not formalised (not needed so far).
- §8: the dual element of Lemma 8.4 is unstar(beta), equal to +-beta* (sign
  (-1)^(pq)); the Cayley determinant is the paper's up to sign.
- Thm 8.9 as stated in the paper ("a gcd which is regular") fails for
  a = 0 in a nontrivial ring; stated as: a = 0, or a regular gcd.
- Thm 8.9 is stated for the 1 x 1 minors D_1(T m) of the last map (its
  entries and 0, Cor88.OneRow) since s (m+1) = 1 is propositional; Cor
  8.10's "finite free resolution of (a, b)" is FFR: a resolution whose last
  map has exactly a, b as nonzero entries; "gcd domain" is proved as: every
  a, b merely have a gcd, regular unless a = b = 0 (no integrality claim).
- Vasconcelos (Thm 2.6) is not used in Thm 8.9 (replaced by the ranks of
  Thm 6.8).
- Gr(beta) >= 2 in §8 is the explicit form of §6 item 2 (GrTwo); the true
  grade from Thm 6.8 is converted by GradeBridge.
