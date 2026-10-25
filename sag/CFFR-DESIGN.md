# Constructive finite free resolutions (cffr.pdf): design for workers A and B

Papers (in /Users/coquand/CANONICITY): `cffr.pdf`, T. Coquand and C. Quitté,
*Constructive finite free resolutions*, Manuscripta Math. 137 (2012),
331–345; and `ctete.pdf`, T. Coquand and C. Tête, *An elementary proof of
Wiebe's Theorem*, J. Algebra 499 (2018), 103–110, whose §1 gives the
elementary characterisation of grade by latent regular elements that cffr
only mentions (after its Lemma 6.5).  Text: `pdftotext -layout cffr.pdf`,
`pdftotext -layout ctete.pdf`.  All paths below are relative
to `unit/sag/`.  Coordinator: the session that wrote this file (it checks,
commits and pushes; workers do not commit).

Status (2026-10-25): design only; nothing built.

## 1. What exists (do not redo; link read-only)

- `exterior/`: Λ(Rⁿ) by its universal property (`ExteriorModel`,
  `ExteriorAlgebra`, `ExteriorUniversal`), degrees (`ExteriorDegree`),
  determinants with matrices given by their columns (`Determinant`:
  det(AB), `Adjugate`: adj(A)A = det A·I), `CharPoly`, `DeterminantTrick`,
  Cayley–Hamilton.
- `exterior/`, **in progress by another terminal (pcc2.pdf, the
  Plücker–Sylvester relation): do not edit, and link only files it has
  finished**: subsets as `ExteriorCoordinates.Index n` with coordinates
  `coeff`/`tab`/`basis`, the duality pairing (`ExteriorDuality`: `dot`,
  `star`, `dual`), the higher adjugate (`ExteriorAdjugate`), contraction by
  a vector (`ExteriorVectorContraction`: `contract`, and `mixed`:
  c_v(w ∧ x) + w ∧ c_v(x) = (v·w) x, which is cffr's interior product
  formula of §5.1 and the homotopy of Lemma 6.1), transposition and
  det Aᵀ = det A (`ExteriorTranspose`), homogeneous parts
  (`ExteriorHomogeneous`).  Its Theorem 1 is cffr's Proposition 8.3.
- `cokernel7/`: modules over a commutative ring (torsor/Alg73 modules),
  linear maps, submodules, kernels, images (`Submodules`), quotients
  (`QuotientModule`), localisation M_r of a module (`Localisation`,
  `LocalisationModule`).
- `horrocks/`: `LocalGlobal` (local–global for comaximal monoids),
  `Regularity`, `MonicRegular` (monic polynomials are regular),
  `LocalFree`.
- `em/Snake`: the connecting map and exactness for a short exact sequence
  of complexes of abelian groups.
- Two notions of commutative ring are in use: `Ring[l].CRing` (exterior,
  pn) and `Alg73.CRing` (cokernel7, torsor), related by
  `bridge7/RingBridge`.  Use `Ring[l].CRing` with `setR` as `exterior/`
  does; cross to modules through `RingBridge` once, in one file.

## 2. Scope (cffr numbering)

All of the paper: §2 (Lemmas 2.1–2.3, Cor. 2.2, Thms 2.4–2.6, Cor. 2.7),
§3 (Thm 3.1), §4 (Lemma 4.1, Cor. 4.2, Lemma 4.3), §5 (the Koszul
complex), §6 (Lemmas 6.1–6.5, Thm 6.4, Prop. 6.6, Lemma 6.7, Thm 6.8),
§7 (Thms 7.1–7.3, Cors 7.4–7.6), §8 (Lemmas 8.1, 8.2, Prop. 8.3,
Lemma 8.4, Cor. 8.5, Lemma 8.6, Thm 8.7, Cor. 8.8, Thm 8.9, Cor. 8.10).

Latent regular elements (needed by Prop. 6.6 and Lemma 6.7, hence by
Thm 6.8 and Thm 8.9) come from ctete §1: Lemma 1, Cor. 2, Lemma 3, Thm 4
(McCoy: c(f) regular iff f regular in R[u₁, …, u_p]; this is cffr's
Thm 3.1), Def. 5 (true grade: a regular sequence of length k in I, maybe
after adding indeterminates), Lemmas 6, 7, Thms 8, 9.  Also in scope:
Wiebe's theorem (ctete Thm 11, Cor. 12), last.  Out of scope: ctete §3
(automatic proofs for fixed n) and Remark 10 (a counterexample).

Open point for the user (B reports before starting it): the comparison of
the true grade with the Koszul grade Gr(a; R) ≥ k of cffr §6, needed to
combine §7 (Koszul grade) with Thm 6.8 (true grade, through Lemma 6.7).
ctete says all of cffr can be reproved with the true grade alone, without
long exact sequences, but does not write those proofs; the plan keeps the
Koszul route for §6.

### B6 report (worker B, 2026-10-25): what each option needs, estimate

State of koszul/: Koszul grade `Grade.Gr E N a k` (Gr(a; E) >= k, any
module E) with Lemmas 6.1–6.5, Thm 6.4, items 1–3; true grade
`TrueGrade.TGr k D m J n I` (ideal I of a ring D, relative to a list J,
sequence form of ctete Def. 5) with ctete Lemmas 1, 3, 6, 7, Cor 2,
Thm 9, base change, Prop. 6.6 and Lemma 6.7.  Where they meet: §7
(Thms 7.1–7.3, Cors 7.4, 7.5) uses Gr(a; E) for MODULES E (Lemma 6.2,
Thm 6.4), while Thm 6.8 concludes Gr(D_r(A_k)) >= k in the TRUE grade
(Lemma 6.7).  Anything that feeds Thm 6.8 into §7–§8 needs at least
true => Koszul for ideals of R.

(A) The comparison, as cffr sketches it (Lemma 6.5 + invariance of the
Koszul grade under adding indeterminates).  The induction runs modulo J, so
it compares TGr k D J a with Gr(a; D/J) >= k (D/J = cokernel7
QuotientModule of D by the ideal of J).
  (A1) true => Koszul.  Induction on k: a witness c in (a) regular mod J
       over D[u], then Lemma 6.5 at E = D[u]/J with x = c (c = b.a,
       b explicit from the membership; c is E-regular = regular mod J).
       Needs: (i) (D/J)/c ~ D/(J, c) as modules and Gr invariant under
       module isomorphisms (functoriality of C(a; -)); (ii) DESCENT of the
       Koszul grade along D -> D[X] for quotient modules: a cocycle over D
       becomes a coboundary over D[X], evaluate at X = 0 (ev0) to get one
       over D; this needs the Koszul differentials over D and D[X] to
       correspond, i.e. exterior coefficients along a ring map (cffr/
       BaseChange gives the exterior model along h).  Estimate: about
       500–700 lines, 4 files, one long session.
  (A2) Koszul => true (the converse).  Additionally ASCENT of the Koszul
       grade along D -> D[X] (a cocycle with polynomial entries: take the
       coefficient of each X^k mod J (cffr/PolyIdeal coefficientwise
       membership), each is a cocycle over D, merely a coboundary, then
       assemble finitely many by choice) and the first step (Gr(a; D/J)
       >= 1 gives a regular mod J: item 1 relative to J).  Estimate: about
       400 more lines.  Needed only if some argument must turn a Koszul
       grade into a true grade (e.g. to apply Lemma 6.7 or Prop. 6.6 to a
       grade obtained in §7).
(B) Restate what A uses from §6 with the true grade.  Lemmas 6.2, 6.3,
    Thm 6.4 are statements about MODULES; with the true grade they need a
    true grade of an ideal on a module (E-regular sequences "maybe after
    adding indeterminates"), hence polynomial extensions E[X] of arbitrary
    modules (not available: only quotients D/J have one for free), new
    proofs of 6.2–6.4 via Cor. 4.2, and §7 rewritten on that notion.
    Estimate: larger than (A), about 1000–1500 lines, and the Koszul
    development B1–B4 becomes unused by §7.

Recommendation: (A1) now (it is what Thm 6.8 -> §7 needs), (A2) only if
A's §7–§8 turn out to need Koszul => true.  Waiting for the user's
decision before starting B6.


Coordinator (A) on the B6 question, 2026-10-25: §8 does not need Koszul =>
true.  §8 uses grade only as Gr(beta) >= 2 in Lemmas 8.4, 8.6, Cor. 8.5 and
Thm 8.7 (the explicit form, item 2 of §6), and those hypotheses come from
Thm 6.8 (true grade) in Cor. 8.8 and Thm 8.9.  So §8 needs true => Koszul
(at k = 2 at least), i.e. (A1).  §7 is stated with the Koszul grade; its
hypotheses (Cor. 7.5, 7.6) are grade conditions on D_k, which Thm 6.8 gives
as true grade, so again (A1).  Recommendation: (A1) now; (A2) not needed for
the scope of CFFR-DESIGN §2.

**User decision 2026-10-25: (A1).**

**Coordinator, 2026-10-25 (after Thm 6.8):** the goal is all of cffr; Wiebe
(ctete §2) waits.  §7 split: B does Thm 7.1, 7.2, 7.3, Cor. 7.4 (Koszul
grade, modules) plus a matrix-level corollary of 7.1 for Cor. 7.5 (B7), and
the transport of the true grade to R[1/x] (B8); A does Cor. 7.5, Cor. 7.6,
then Thm 2.6, Cor. 2.7, then §8 when the pcc2 terminal has Prop. 8.3.

## 3. Two workers

| | owns | first track | after the join |
|---|---|---|---|
| **A** | `cffr/` | §2 (regularity, McCoy, Vasconcelos), ctete Thm 4 (= cffr Thm 3.1), Lemma 4.3 | Thm 6.8, §7, §8, Wiebe (ctete §2) |
| **B** | `koszul/` | complexes of modules and their long exact sequence, §4 (4.1, 4.2), §5, §6 up to Lemma 6.5 | true grade (ctete §1, with A's Thm 4), Prop. 6.6, Lemma 6.7; the comparison with the Koszul grade after the user's decision |

Join points:
- B needs from A: regular finitely generated ideals and Lemma 2.3 (for
  Lemma 6.7), and A's minors for Thm 6.4's matrix.
- A needs from B: Gr(a; E) ≥ k with Lemmas 6.2, 6.3, Thm 6.4 (for §7) and
  Lemma 6.7 (for Thm 6.8).
- §8 needs the Plücker–Sylvester relation (Prop. 8.3) from the pcc2
  terminal: do not prove it again; link it when it is announced.
Each side announces finished, stable files in `CFFR-INTERFACE.md`; the
other side links them (never edits them).

## 4. Representation choices

- **Rings and ideals.** `Rg : Ring[l].CRing`, `setR`.  A finitely generated
  ideal is a list `a : Fin n -> R`.  "a is regular for E" (paper §2) is
  `(x : E) -> ((i : Fin n) -> a i · x = 0) -> x = 0`.  The trivial ring is
  `Id R one zero`.
- **Matrices** are lists of columns, as in `exterior/Determinant`: a map
  Rᵖ → R^q is `u : Fin p -> Vec q`.  **Minors are exterior coordinates**:
  the k × k minors of A are the coordinates of u_{i₁} ∧ ⋯ ∧ u_{i_k}, i.e.
  `coeff` of the products of generators (this is how §8 writes ∧ᵏ(A)).
  So 𝒟_k(A) is the list of these coordinates, indexed by pairs of subsets
  of size k.  Do not define submatrix determinants separately (one name
  per notion); if pcc2's Lemma 5 gives the comparison with submatrix
  determinants, link it.
- **"Stable of rank p"** (§2.1): 𝒟_{p+1}(A) = 0 and 𝒟_p(A) regular.
- **Localisation at aᵢ** (Lemma 2.3, Thms 2.4, 2.6, 6.8, Cor. 7.5): the
  ring R[1/a] and modules M_a from `cokernel7/Localisation*`; Lemma 2.3 is
  the local–global principle that replaces minimal primes, and should be
  stated once, generally, and used everywhere.
- **Finite free complexes**: a list of matrices `A k : Fin (p k) -> Vec (p (k-1))`
  with A_{k-1} ∘ A_k = 0; exact = kernel in the image at each stage.
- **The Koszul complex** (§5.2): C(a; E) = functions `Index n -> E`
  (coefficients of the e_I), graded by |I|, with d α = a ∧ α.  Define it
  from the exterior product, not by a sign formula on subsets; then
  Lemma 6.1 is `mixed` (contraction by b with b·a = x).
- **Grade.** Gr(a; E) ≥ k iff Hⁱ(a; E) = 0 for i < k (paper §6), as a
  proposition; also the explicit forms for k = 1, 2, 3 (paper §6, items
  1–3) as lemmas.  Long exact sequences in the vanishing form suffice
  (cohomology groups are only needed through "= 0").
- **Adding indeterminates** (ctete): R[u] one variable at a time, from
  `sag/polynomial` and `pn/PolynomialRing` (check what exists; reuse).  Prove
  McCoy for one variable and iterate, rather than with monomial orderings.
  Regularity is invariant under R → R[u] (ctete §1, first remark).
- **True grade** (ctete Def. 5) as an inductive proposition on k: Gr(I) ≥ 0
  always; Gr(I) ≥ k + 1 iff merely, after adding finitely many
  indeterminates, some regular a in I has Gr(I) ≥ k modulo a.
- **No decidable equality on R** is assumed anywhere (the paper is
  constructive); no prime ideals.

## 5. Rules (as for CCA)

- Checker: the `unit` checkout (`/Users/coquand/CANONICITY/unit`):
  `cabal build` at its root at the start of a session; check with
  `./segc sag/DIR changed|all` from that root.  Every file < 10 s; every
  shell command < 60 s, with a timeout; bounded loops.
- Write so that checking follows reading:
  `/Users/coquand/CANONICITY/seg/WRITING.md`.  The informal proof first, in
  the file comment, matched to the declarations; one name per notion;
  "by definition" facts as `refl` lemmas next to the definition; accessors
  instead of projection chains; **name a module instance once**
  (`module MI = M[a, b]`) rather than writing `M[a, b]` at each use (each
  written instance is checked where it is written).
- After each file run `--opened` and look at the TOTAL openings (the sum of
  the `*N` counts); record in your HANDOFF any declaration above 500 with
  its cause.  Write `--opens` files for the main declarations.
- Recursion only through eliminators (`unit/doc/PRIMREC.md`); no type
  classes; no HITs; general statement first, instance second; lock a
  construction right after its characterising lemmas.
- Each worker edits only its own directory; shared files (`exterior/`,
  `cokernel7/`, `horrocks/`, `pn/`, `em/`, …) are read-only, linked.  A
  needed change to a shared file: ask the coordinator.  Do not commit.
- Keep a "Gaps" section in your HANDOFF: statements of the paper used
  without proof, omitted verifications, citations replaced by proofs.
  Already seen: Prop. 8.3 is proved "in the generic case" via a field of
  fractions (the pcc2 terminal proves it without); footnote 5 corrects
  Northcott Ch. 7 Lemma 2.
- Report to the coordinator at each milestone, with cold runs of your
  directory, the totals above 500 and what you announced.
