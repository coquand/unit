# wiebe: Wiebe's theorem (ctete §2, Theorem 11 and Corollary 12)

T. Coquand, C. Tête, *An elementary proof of Wiebe's Theorem*
(`ctete.pdf`), §2, relative to a list J as the rest of the cffr/ctete
formalisation (no quotient rings).  Log: `../HANDOFF-WIEBE.md`; design:
`../CFFR-DESIGN.md` §4–§5.  Check from the `unit` root:
`./segc sag/wiebe all` (168 modules, about 2.6 s cold; every wiebe file
under 0.1 s; at most 226 openings per declaration; `Wiebe.opens` checks
the main declarations).

Linked read-only: the pn foundation, `exterior/` (Determinant, Adjugate,
ExteriorTranspose, DeterminantTrick, Naturality), `cokernel7/`, `em/`,
`cffr/` (RegularIdeal, PolyRegular, PolyRegularMod, PolyIdeal) and
`koszul/` (TrueGrade, TrueGradeIdeals, TrueGradeThm9, TrueGradeBase).

## Statement

Ring `Rg` with `setR`; a, b : `Fin n -> R`; V : `Determinant.Over.Mat n`
with b = V a mod J (`WiebeMatrices.Hyp m J n a b V`: b_j − Σ_i a_i V i j
in (J)).  So `V i j` is ctete's V_ij (the columns of the `Mat` are the rows
of ctete's V), and Δ = `det n V`.  Lists: (J, b) = `WiebeLists.cat n b m J`
(b_n outermost), (J, b, a) = `cat n a (plus n m) (cat n b m J)`,
(J, b, Δ) = `TrueGrade.extend` of (J, b) by Δ.

| ctete | statement | declaration |
|---|---|---|
| Thm 11 (⊆) | Gr(b) ≥ n mod J: x Δ ∈ (J, b) ⇒ x ∈ (J, b, a); x a_i ∈ (J, b) ∀i ⇒ x ∈ (J, b, Δ) | `Wiebe.theorem11 n D m J a b V h g : WiebeCore.Concl ..` (`Perp`, `Ann`) |
| Thm 11 (⊇) | Δ a_i ∈ (J, b) (Cramer), so (a) ⊆ Δ⊥ and (Δ) ⊆ (a)⊥, for any V | `Wiebe.Over.Thm11[m,J,n,a,b,V,h]`: `delta-a`, `a-in-delta-perp`, `delta-in-a-perp` |
| Thm 11 | Δ⊥ = (a) and (a)⊥ = (Δ) mod (J, b) | `Thm11.WithGrade[g]`: `delta-perp-in`, `a-perp-in`, `delta-perp`, `a-perp` |
| Cor 12 | the same when b is a regular sequence mod J (`TrueGrade.RegSeq`) | `Thm11.WithSequence[rs]`: `delta-perp`, `a-perp` |

## Proof (files)

| step (HANDOFF-WIEBE) | declaration |
|---|---|
| lists (J, c), inclusion by generators, (J, y, c) = ((J, c), y), x ∈ (J, c) ⇒ t + (J) with t ∈ (c), congruence mod (K) | `WiebeLists` (`cat`, `included`, `cat-ext`, `cat-split`, `Mod`) |
| 1, 4: Cramer Δ a_n = δ b_n mod (J, b_<n), δ = det W = adj(V)_nn (block), b_<n = W a_<n mod (J, a_n) | `WiebeMatrices` (`Cramer.result`, `BlockDet.result`, `HypBlock.result`) |
| elementary operations E = I + e_r wᵀ (w_r = 0): det E = 1, inverse, on b (`BOp`) and on a (`AOp`) | `WiebeMatrices` (`eop`, `emat`, `det-emat`, `eop-inv`, `rel-same`) |
| 5, 6: the two inclusions at n+1 from n (in one ring, generic position assumed); n = 0 | `WiebeCore.Step.result`, `WiebeCore.base` |
| regular sequences read backwards (rot), last term replaced, congruent terms, Gr(I) ≥ k ⇒ Gr(I') ≥ k when I ⊆ (J, I'); good ring maps (keep regularity, have a retraction) | `WiebeSequences` (`rs-last`, `replace-last`, `tgr-rot`, `regseq-cong`, `TgrSub`, `Good`, `down`) |
| chains of operations on b: same ideal, b = V a mod J kept with det V, along ring maps, lifted past an inserted term | `WiebeChain` (`Chain`, `chain-same`, `chain-hyp`, `ChainMap`, `lift`) |
| 2 (b): generic change b_i ↦ Kronecker polynomials (ctete's u_i), b_n last of a regular sequence | `WiebeGeneric.generic` |
| conclusions: propositions, depend only on (J, b), (J, a), Δ; along ring maps with retraction | `WiebeTransfer` (`concl-prop`, `Transfer`, `Map.Down`) |
| 2 (a), 3, the induction | `Wiebe.Induction` (`fa` Kronecker of a, `g5` by Theorem 9, `WithV.result`) |
