# Handoff: Ag.seg — Section 4.4 DONE (§4.5 started: HANDOFF-WW.md)

State (2026-10-27): `Ag.seg` (Def. 4.18 – Lemma 4.24) green, no postulates,
checked with `segd Ag.seg --opens Ag.opens`: all 100 declarations listed,
nothing else opened. Mirror `tools/otag.py lem 6`. Findings in README Step 4.

Ag interface (for §4.5 – §4.7):
- `Ag A = Seg A (W A)`; parts `ag-ot`, `ag-w` (A ⊆ W(A)), `ag-back`
  (y ∈ W(A), y ≼ x ∈ A ⟹ y ∈ A), `ag-cap` (A ∩ x = W(A) ∩ x), `ag-M`,
  `ag-h17` (4.17(b)'s hypotheses at any k ∈ A).
- `Prog`, `Prog1`, `rem421a` (the induction of Notation 4.22), `rem421b`,
  `rem421c`; `Imp A B` = {y | y ∈ A → y ∈ B}.
- `Aplus`, `rem423a` (DC A, UC A (Dn A)), `rem423b`, `rem423c`.
- `rem424` with `H24`; transfer `wa-at`; `eq-ag` (A = W(A) ∩ a ⟹ Ag(A)).
- Segments: `seg-in`, `seg-dn`, `seg-cap`, `seg-trans`, `seg-eqv`;
  `ag-eqv`, `prog-eqv`, `aplus-eqv` (Remark 4.19(b)).

Next: §4.5 (pp. 147–148): Def. 4.25 𝒲, Lemma 4.26 – 4.31. New file
`WW.seg`. Read the page images first (PDF page = printed − 112).

The design question to settle first (size): 𝒲 = ⋃{X : 𝒫(N) | Ag(X)}
quantifies over sets, so in Unit it is `(X : Cl) * (Ag X * X y)`, a class at
level gl+ (sets X at gl). Lemmas 4.27 – 4.31 use W(𝒲), M(𝒲), τ^𝒲, C^a(𝒲),
so CA/WA/Clos/Lem417/Ag are needed at the level of 𝒲 too (modules are
parametrised by the level: `WA[gl+]`?) and a statement mixes the two levels
(Lemma 4.26(a): Ag(X) ↔ X ⊑ 𝒲, X at gl, 𝒲 at gl+). Check how Unit handles
a module opened at two levels before writing anything. Lemma 4.30 also picks,
for each y ∈ B, a set g(y) with Ag(g y) and y ∈ g y (choice from the
Σ-witness, fine in type theory), and its C is a union over B̂.

Uses ahead: 4.28(b) Ag(A ∩ y) (by 4.13(b) and 4.24's style); 4.29 uses
4.23(a), (b), (c) at A ∪ B (Ag(A ∪ B) from 4.26); 4.31 uses 4.29(c) and
4.30.

Checker conventions (keep them): those of HANDOFF-CLOS.md, plus
- an implicit `sym`/`subst` next to `g : Ag A` opens Ag and Seg: named
  transports (`cap-trs`, `tr-Bs`, `le-eq`);
- a term `ag-ot A g x ax` inside `rem214f` projections opens Ag: pass
  `ox : OK x` as a parameter (`up-below-at`, `wap-ok`);
- names to check against all imports (Clos has `seg-back`).
