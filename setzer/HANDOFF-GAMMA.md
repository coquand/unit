# Handoff: GammaI.seg — Section 4.6 DONE (Def. 4.32 – Lemma 4.38); §4.7 next

State (2026-10-28): `GammaI.seg` green, no postulates, 72 declarations of its own (1466
with imports, 0.40 s), `segd GammaI.seg --opens GammaI.opens`: all listed, nothing else
opened. Mirror `tools/otgam.py lem 7` / `xlem 6` (no failures). Informal proofs in the
header of GammaI.seg (including why Gamma' differs from Setzer's D1-D5).

## Interface

- `Hq c` = OK (psi_I c) * tau^WW(psi_I c) c WW; `hq-of c s` from s : A^WW(WW)(psi_I c).
- `CW c` = C_I^WW(c); `Gam c h X p` = Gamma'(X); `it c h n` stage n (set, proof);
  `Stage c h n d`, `Gw c h d` = Gamma^w (a set), `rem437 c h x` : x in CW => x in Gamma^w.
- 4.38: `rem438a c (s : scA WW WW (psi ii c)) : WW (psi ii c)`,
  `rem438b x (s : scA WW WW x) (l : LT x ii) : WW x`,
  `rem438c : Eqv (Cap WW ii) (Cap (WA[ul+].WA WW) ii)`.

## Next: Section 4.7 (p. 151-152), Def. 4.39, Lemma 4.40, Theorem 4.41

WW_0 = WW n I, WW_{i+1} = W(WW_i) n Omega_{I+1+i}; Lemma 4.40 (meta induction on i):
Ag(WW_i), Omega_{I+i} in WW_{i+1}, WW_i = WW_{i+1} n Omega_{I+i}. Theorem 4.41 from 4.21(c),
4.23(b). Sizes: every WW_i is a class (ul+); W of a class at ul+ is WA[ul+].WA.
Setzer's step "for all x in tau(I)^WW ... by an easy induction on length(x)" will need a
structural replacement as in 4.37.

Checker conventions: those of HANDOFF-WW.md, plus: the class WW is `WW[gu].WW` in a file
importing module WW; `lt-up` is ambiguous (Ag's vs WW's); never reuse an imported level
name; check new names against imports (silent shadowing).
