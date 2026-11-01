# Handoff: Clos.seg + Lem417.seg — Section 4.3 DONE (§4.4 done too: HANDOFF-AG.md)

State (2026-10-27): `Clos.seg` (Def. 4.14 – Lemma 4.17(a)) and `Lem417.seg`
(Lemma 4.17 (b), (c)) green, no postulates; both checked with
`segd F.seg --opens F.opens`: every declaration listed, nothing else opened.

Lem417 interface (for §4.4 – §4.6):
- `H17 A k` = A ⊆ M(A), k ∈ OT, A ∩ k = W(A) ∩ k (accessors `k-m`, `k-ok`,
  `k-e`, `k-ot`, `k-aw`, `k-wa`, `k-seg`).
- `rem417b A k h : DC (W(A) ∩ k⁺) * UC (W(A) ∩ k⁺) (Bnd k⁺)`, and its parts
  `w-sum`, `w-phi`, `w-om`, `w-ii` (any split for sums).
- `rem417c A hA k y z wk wy wz (k ≼ z) (y ≼ z) (W(A) ∩ z̃ = A ∩ z̃) (k ∈ R)
  (y ∈ C_k(y)) : ψ_k y ∈ W(A)`; the claim `claim A t h wt` (Ind(y ∈ W(A))).
- Cardinal tools: `card-le`, `til-self`, `km-below`, `til-km`, `til-psiR`,
  `til-psiI`, `le-antisym`, `in-Cb` (b ≺ t⁺, v ∈ W(A) ⟹ v ∈ C^b(A)).

Next: §4.4 (pp. 146–147): Def. 4.18 Ag(A), Prog, A⁺; Remark 4.19, 4.20;
Lemma 4.21; Notation 4.22; Lemma 4.23, 4.24. New file `Ag.seg`; read the
page images first (PDF page = printed − 112), write the informal proof in the
header, test on a mirror, check with `--opens`.

Checker conventions (keep them):
- A `let`-bound TERM is opened like an alias: write the term.
- `abT`/`abF` with C^a(A) in the goal opens C: `absurdT`/`absurdB` with the type.
- Implicit-argument `trans`/`subst`/`ap`/`sym` next to a package hypothesis
  opens the package (and W(A)): use named transports with explicit arguments
  (Lem417 `lt-r`, `lt-l`, `le-l`, `tr-b`, `tr-bs`; CA `ca-el`, `ca-el-r`).
- A declaration with an imported name shadows it silently: check new names
  against the imports.
- The class W(A) is `WA[l].WA` in a file importing module WA; level names
  must be fresh per file (Clos `kl`, Lem417 `pl`).
