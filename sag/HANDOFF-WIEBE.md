# Wiebe's theorem (ctete.pdf §2: Theorem 11, Corollary 12)

Last step of the cffr/ctete formalisation (CFFR-DESIGN.md §2, step A7).
Everything else (cffr §2–§8, ctete §1) is done and committed (b931c5b).
Read first: `ctete.pdf` §1 (Def. 5, Thm 9) and §2 (Thm 11, Cor. 12), text by
`pdftotext -layout /Users/coquand/CANONICITY/ctete.pdf` into the scratchpad;
`sag/CFFR-DESIGN.md` §4–§5 (representations, rules); `sag/CFFR-INTERFACE.md`
(what exists, with exact names); `/Users/coquand/CANONICITY/seg/WRITING.md`.

## Where to work

New directory `sag/wiebe/` (own `All.seg`, written like `koszul/All.seg`:
symlinks to the files it needs from `koszul/`, `cffr/`, `exterior/` and their
dependencies; copy `koszul/All.seg`'s import order and append).  `koszul/`,
`cffr/` and `exterior/` are read-only (exterior is frozen, checksums in
`cffr/EXTERIOR-FROZEN.sha256`).  Check with `./segc sag/wiebe changed|all`
from `/Users/coquand/CANONICITY/unit`.  Every shell command under 60 s with a
timeout; every file under 10 s; do not commit (report to the user).

## Statement

a_1..a_n, b_1..b_n in R with (b) = (a) V, V an n x n matrix, Δ = det V.
If Gr(b) >= n (true grade, `TrueGrade.TGr n D zero J0 n b`), then modulo (b):

- Δ⊥ = (a):  x Δ in (b)  =>  x in (a, b)   (and conversely, since Δ(a) ⊆ (b));
- (a)⊥ = (Δ): x a_i in (b) for all i  =>  x in (Δ, b)   (and conversely).

State everything relative to a list J (as the true grade of koszul/ is:
"mod J" = `RegularIdeal.modulo` of `Generated`), with no quotient rings:
membership "x in (L)" is `RegularIdeal.Generated[Rg,m,L].In x`.  Cor. 12 is
the instance where b is a regular sequence (`TrueGrade.RegSeq`, which gives
`TGr n` directly).  Say "proportional / Δ⊥" with explicit membership
statements, both inclusions as separate lemmas, then the two equalities.

## Proof (ctete, Thm 11), induction on n, everything mod J

1. Δ(a) ⊆ (b) by Cramer: adj(V) V = Δ I (`exterior/Adjugate`,
   `Adjugate.Over.adj-mul` or `ExteriorCramerIdentity`; worker B's
   `koszul/Vasconcelos.Zero` already did a Cramer step with
   `ExteriorTranspose` + `ExteriorAdjugate`, reuse its pattern).
2. Generic change of b and a_n by new indeterminates u (R[u], `PolyRegular`,
   `TrueGrade.ext`, `TrueGradeBase.base-change`): b_i -> b_i + Σ_{j>i} u.. b_j
   and a_n -> a_1 u^(n-1) + ... + a_n, which does not change Δ (unitriangular
   change of V); then a_n and b_n are regular mod (b_1..b_(n-1)) (McCoy /
   Kronecker: `PolyRegularMod.Kronecker`, `TrueGradeThm9.Lemma7`).  The
   conclusion is a membership of an element of R, so it comes back from R[u]
   to R by taking the constant coefficient (`cffr/PolyIdeal.to-coefficients`,
   `PolyRegular.ev0`).  This is the costly step; write it once, generally.
3. Thm 9 (`TrueGradeThm9.thm9`): Gr(b_1..b_(n-1)) >= n-1 modulo a_n
   (i.e. relative to J' = (J, a_n): `TrueGrade.extend`).
4. Mod (J, a_n): (b_1..b_(n-1)) = (a_1..a_(n-1)) W, W the top-left
   (n-1)x(n-1) block of V, δ = det W.  Mod (b_1..b_(n-1)) (relative to
   (J, b_1..b_(n-1))): (0,..,0,b_n) = (a) V, so by Cramer Δ a_n = δ b_n.
5. First inclusion: xΔ in (b) => x δ b_n = xΔ a_n in (a_n b_n) mod (b_<n);
   b_n regular => xδ in (a_n); i.e. mod (J,a_n): xδ in (b_<n); induction:
   x in (a_<n) mod (J, a_n), i.e. x in (a) mod J.
6. Second inclusion: x a_i in (b) => x a_n = y b_n mod (b_<n); x a_n a_i =
   y b_n a_i in (a_n b_n) => (b_n regular) y a_i in (a_n) for i < n; so mod
   (J, a_n), y(a_<n) ⊆ (b_<n); induction: y in (δ, b_<n) mod (J, a_n);
   so x a_n = y b_n in (δ b_n, a_n b_n) = (Δ a_n, a_n b_n) mod (b_<n);
   a_n regular mod (b_<n) => x in (Δ, b_n) mod (b_<n), i.e. x in (Δ, b).

Base n = 0: Δ = 1, (a) = (b) = 0: both statements are trivial.

## Tools (names in CFFR-INTERFACE.md)

- True grade: `TrueGrade` (`TGr`, `RegEl`, `RegSeq`, `extend`, `ext`, `mono`),
  `TrueGradeThm9` (`thm9`, `Lemma6`, `Lemma7`, `gr1-to/from`),
  `TrueGradeIdeals` (`Plus`: x in (J, a) iff x - a w in J; `same-id`),
  `TrueGradeBase` (base change to D[X], `theta`), `TrueGradeIso`.
- Regularity: `cffr/RegularIdeal` (`modulo`, `Generated`, `IdealLaws`),
  `koszul/RelRegular` (ctete Lemma 1, Cor 2, Lemma 3 mod any ideal).
- Polynomials: `cffr/PolyRegular`, `PolyRegularMod`, `PolyIdeal`, `PolyMcCoy`.
- Determinants: `exterior/Determinant` (det(AB)), `Adjugate` (adj A A =
  det A I), `ExteriorAdjugate`, `ExteriorCramerIdentity`, `ExteriorTranspose`
  (det A^T = det A).  The block W of V and det W: `Adjugate` has the
  replacement/expansion along a column; check what exists before proving a
  Laplace expansion (the δ relation only needs Cramer for the system
  (0,..,0,b_n) = (a)V, i.e. the last column of adj(V) is δ e_n-like up to
  the cofactors; prove "Δ a_n = δ b_n mod (b_<n)" directly from adj(V) V =
  Δ I and the last row of adj(V) whose last entry is δ).
- §8 has `cffr/Lemma86` (`Divides`, `RegularElement`) if useful.

## Done when

`./segc sag/wiebe all` checks, every file < 10 s, `--opened` totals < 500
per declaration (else record the cause here), and `sag/wiebe/README.md`
states ctete Thm 11 and Cor 12 with their declarations.  Record gaps
(statements used without proof) in this file.

## Progress

(append here)

### 2026-10-25: done (not committed)

`sag/wiebe/` checks: `./segc sag/wiebe all` cold 168 modules, 0 failed,
2.64 s; the eight wiebe files each under 0.1 s.  Openings (`--opened`):
maximum 226 per declaration (`WiebeMatrices.BlockDet.result`, the
Ext(n+1) = Ext(n) x Ext(n) computation of det V[n <- e_n]); nothing above
500.  `Wiebe.opens` (main declarations) checks clean.  `exterior/`
checksums unchanged; nothing outside `wiebe/` edited.

Files (import order): `WiebeLists`, `WiebeMatrices`, `WiebeCore`,
`WiebeSequences`, `WiebeChain`, `WiebeGeneric`, `WiebeTransfer`, `Wiebe`;
linked in addition to koszul's list: exterior `ExteriorRelation`,
`Naturality`, `CharPoly`, `DeterminantTrick`.  Statements and the map
from the proof steps to declarations: `wiebe/README.md`.

Main declarations: `Wiebe.theorem11 n D m J a b V h g` (the inclusions
Delta-perp in (a), (a)-perp in (Delta), mod (J, b), for Gr(b) >= n mod J);
`Wiebe.Over.Thm11[m,J,n,a,b,V,h]` (converse inclusions by Cramer, any V;
`WithGrade[g].delta-perp`, `.a-perp`: the two equalities;
`WithSequence[rs]`: Corollary 12).

Choices that differ from the plan above:
- Hypothesis "(b) = (a) V" is b = V a mod J with V a column list
  (`b_j = sum_i a_i V i j`), so Cramer is adj(V) V = det V . I as in
  exterior/Adjugate, without transposes; det is the same.
- The generic change of b is a chain of elementary operations
  eop r w (add sum_l w_l b_l to b_r, w_r = 0), carried along the ring maps
  of the construction; each keeps (J, b) and b = V a mod J with det V
  (V -> E V, det E = 1 by Adjugate's linear form b |-> det I[r <- b]).  The
  change of a_n is one such operation on a (V -> V E^-1).  No triangular
  determinant or block-insertion lemma is needed.
- The rings reached by adding indeterminates are handled abstractly: a
  "good" map D -> T keeps regularity mod lists and has a retraction (the
  constants D -> D[X] with evaluation at 0; composites).  The generic step
  is stated in continuation form for any proposition P, so no type of
  rings is truncated.
- Order in ctete's step: Gr(b1_<, fa) >= n+1 mod J from the regular
  sequence b1_n, ..., b1_1, fa (the last term of the generic sequence
  replaced by fa, regular mod (J, b1_<) by McCoy), then Theorem 9 with fa,
  then dropping fa mod (J, fa) (TgrSub).

Gaps: none.  Every statement used is proved here or in the linked
directories (ctete Thm 9 = koszul/TrueGradeThm9.thm9; McCoy mod J =
cffr/PolyRegularMod; det(AB), adj, det-transpose, naturality = exterior/).
