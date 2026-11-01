# Handoff: WW.seg — Section 4.5 DONE (Def. 4.25 – Lemma 4.31); §4.6 next

State (2026-10-27): `WW.seg` green, no postulates, 140 declarations of its own
(1383 with imports, 0.37 s), checked with `segd WW.seg --opens WW.opens`: all
listed, nothing else opened. Mirror `tools/otww.py lem 6` (statements) and
`tools/otww.py proof 6` (the steps of 4.30, 4.31 with any distinguished set D in
place of WW; no failures). The informal proofs are in the header of WW.seg.

## The size question (settled)

Setzer's WW = U{X : P(N) | Ag(X)} quantifies over sets, so it is a class. In
Unit:

- A declaration's arguments include every level in scope at it, so a data type
  or function declared after `level a ;` has one copy per instance:
  `OT[l].T` and `OT[l+].T` were different types (and the checker overran
  comparing them instead of failing — a checker defect to report).
- Fix (refactor, all files re-checked green, `--opens` clean): **OT.seg is
  level-free**, like the core's `Base.seg`. It now also holds the executable
  definitions of OTC/OTF (`isOne pred1 omF kminus arg`, `N one consA add suc
  mul phiF omN cardS card tilde up mFi pFi mI cat`) and `One`. "if" is written
  per type: `ifB ifT ifL ifQ` (lemmas `ifT-t/f`, `ifL-t/f`, `ifQ-t/f` in OTC,
  `ifQ-G` in OTF; `iteC`, `ite-L`, OTTrans `iteT/iteF` restated for them).
  The generic `ite (A : U l)` and `B2` moved to OTLaws. Every file does
  `open OT ;` (no level). `.opens` updates: CA `g-psi-lo/hi` (ifL), Clos
  `mfi-one add-zero card-psi-I card-psi-R card-phi` (ifT/ifQ, card-phi + C4).
- WW.seg opens the Section 4 files at `ul+` (classes) and uses the instances
  `SC = CA[ul]`, `SW = WA[ul]`, `SG = Ag[ul]` for sets. Predicates `OK LT Cap
  Bar` of the two levels are equal by definition (`ok-up`, `lt-up`, `cap-up`,
  `bar-up` and `-dn`). The data built per level (Or, the W-type) are related by
  lemmas: (L1) `lc` (C^a(X) set = class), (L2) `lw-up`, `lw-dn` (W(X)),
  (L3) `ag-up`, `ag-dn`. A set as a class is `Lf X` (Pi types are not
  cumulative: `T -> U ul` is not `T -> U (ul+)`).

## WW interface (for 4.30, 4.31, Section 4.6)

- `WW y = (X : SC.Cl) * (SG.Ag X * X y)`; parts `ww-set`, `ww-sag` (Ag as a
  set), `ww-gag` (as a class), `ww-mem`; `ww-mk X (g : Ag (Lf X)) y xy`;
  `ww-ot : Sub WW OTc`.
- 4.26: `ww-seg X g : Seg (Lf X) WW`, `ww-ag-cl B s : Ag B`, `ww-ag-set`;
  uniqueness `agree` (from 4.24 with a_0 = a_1 = c+1, via `bar-eq`); transfer
  at a bar `bar-w`; `bar-cap`, `le-bar`.
- 4.27 `ag-ww : Ag WW`. 4.28 `rem428a A (H : x in A -> Cov A x)`, `rem428b A g c oc
  : Ag (Cap A c)`.
- 4.29 `rem429a : DC WW * UC WW (Dn WW)`, `ww-up` (m in WW => m+ in WW),
  `rem429c` (Omega_x => Omega_{x+1}), `rem429b-sum/-phi/-psi` (forms y + z,
  phi_y z of Def. 2.10, psi_y z in OT). Bound: `card-add`, `card-phi`
  (`CardOf x y z`: card x = card y or card z), `bound` (y, z <=' m => x <' m+).
- Findings: 4.29(b)'s printed "z <=' C, z in C" is "x <=' C, x in C"; proved
  by a shorter route than Setzer's (A u B)+ (header of WW.seg); the bound
  y + z, phi_y z <' max{y,z}+ is left implicit by Setzer and proved here.

## Lemmas 4.30, 4.31 (done)

- 4.30 `rem430 a B (h : H430 a B) : WW a`, H430 a B = a in M(WW), a <' I,
  B c WW|a (Sub (Lf B) (Bar WW a)), tau^WW(a) <=' B (Sub (tau WW a) (Dn (Lf B))).
  C = U_p (g p n a) is `Cu`, C u {a} is `Cua`; steps `ag-cu` (4.28), `tau-ww`,
  `cu-eq` (C = WW n a), `wc-c` (W(C) n a c C), `cua-eq` (C' = W(C') n (a+1)).
  Setzer's Ind(d in W(C)) is not needed (wc-c uses no induction hypothesis).
  `ww-zero` (0 in WW: 4.30 with B empty), `ww-one`.
- 4.31(a) `rem431a x (w : WW x) (l : LT x ii) : WW (omF x)`, by `rem421a` with
  `Om431`; non-fixed case is 4.30 with `Bom` = {Omega_{y+1} | y in A n a}.
  FINDING: Setzer's "a in C^a(WW) c C^{Omega_a}(WW)" is the wrong inclusion
  (4.7(b) gives C^{Omega_a} c C^a; psi_{Omega_1} 0 in C^1({0,1}) \
  C^{Omega_1}({0,1})); proved instead by a in WW n Omega'_a c C^{Omega_a}(WW)
  (4.7(h), `lt-om`).
- 4.31(b) `rem431b0 : WW (psi ii zero)`, `rem431b x (w : WW (psi ii x)) :
  WW (psi ii (suc x))`; both `fi-ww c e (f : Fb c e)` with B = {W_n} (`Bw`).
- Reusable: `cap-ag` (4.28(b) for a set), `cap-of` (A = B n a, b <=' a =>
  A n b = B n b), `ag-ca` (Ag(A) => C^b(A) downward and upward closed),
  `mI-lo`, `om-in` (Omega_s in X downward closed => s in X), `s-lt`, `w-lt`,
  `w-mono`, `lt-psiS`, `lt-sucS`, `x-in`, `xs-in`.

## Next: Section 4.6 (p. 149 ff.), Gamma_c

Goal (Lemma 4.38(a)): W(WW) n I = WW n I, via A^WW(WW) n I c WW, which by
4.31(b) reduces to psi_I c in A^WW(WW) -> psi_I c in WW (**), and by 4.30 to
C^{psi_I c}(WW) n psi_I c being a set (***), proved via C_I^WW(c) =
C_I(c) n C^{psi_I c}(WW) as a least set with clauses (B1)-(B5)/(D1)-(D5).
Read pp. 149-152 from the page images (PDF page = printed - 112).

Checker conventions: those of HANDOFF-CLOS.md / HANDOFF-AG.md, plus
- in WW.seg the classes `WA`, `Ag` are `WA[ul+].WA`, `Ag[ul+].Ag` (module
  names); level names: `ul` is used here;
- `A * B -> C` parses as `A * (B -> C)`: parenthesise products before `->`.
