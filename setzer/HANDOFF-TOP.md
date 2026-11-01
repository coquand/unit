# Handoff: Top.seg — Section 4.7 DONE (Def. 4.39 – Theorem 4.41); Section 4 complete

State (2026-10-28): `Top.seg` green, no postulates, 56 declarations of its own (1533 with
imports, 0.42 s), `segd Top.seg --opens Top.opens`: all listed, nothing else opened.
Mirror `tools/ottop.py lem 6` (88 terms, WW_0 .. WW_3; no failures). Informal proofs in
the header of Top.seg.

## Interface

- `iN n` = I + n, `kN n` = Omega_{I+n} = omF (iN n); `kN-up m : up (kN m) = kN (ns m)`,
  `lt-k m : kN m <' kN (ns m)`, `kN-ok`.
- `WWi : N -> Cl` (Def. 4.39); `EI n` = (WW_n = W(WW_n) n Omega_{I+n}), `FI n` =
  Omega_{I+n} in W(WW_n); `inv n : EI n * FI n`.
- `rem440 i : Ag(WW_i) * (Omega_{I+i} in WW_{i+1} * WW_i = WW_{i+1} n Omega_{I+i})`.
- `thm441c n B (p : ProgOT B) y (oy : OK y) (l : y <' psi_{Omega_1} Omega_{I+n}) : B y`
  (B a class), `thm441` for a set X (class Lf X).
- `tau-I : tau^WW(I) c WW` (no induction), `psi-ww n : psi_{Omega_1} Omega_{I+n} in WW_{n+1}`.

## Findings

- Setzer's two "easy inductions on length(x)" (F(0) and F(j+1)) are not needed: F(0) from
  4.20 + 4.7(b) below psi_I 0 or psi_I(b+1) (b from 2.14(g)); F(j+1) from 4.23(c) for
  WW_{j+1} and the transfer lemma at Omega_{I+j+1}.
- 4.13(b) in the step needs WW_{j+1} c M(WW_{j+1}), not stated: WW_{j+1} c W(WW_j) c
  M(WW_j) c M(WW_{j+1}).
- n is internal (recursion N -> Cl uses a universe above the classes; Setzer's n is meta).

## Possible next steps

- Corollary 4.42 (lower bound statement) is about the theories; nothing to formalise here
  beyond Thm 4.41.
- The upper bound side (ML1W -> KPI+) stays out of Unit (see the project memory).
