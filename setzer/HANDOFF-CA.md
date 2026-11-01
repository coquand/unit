# Handoff: CA.seg, block 1 (Section 4.2) DONE

State (2026-10-27): `CA.seg` green (756 declarations with imports, 0.25 s),
`segd CA.seg --opens CA.opens`: every declaration of CA.seg is listed and
nothing else is opened. No postulates, no hypotheses beyond the stated ones.

Done: C^a(A), Assumption 4.4 (= Lemma 5.5), Def. 4.5, Remark 4.6(b),
Lemma 4.7 (a)-(h), Lemma 4.9 (a)-(e).

Statements as proved (see the CA.seg header):
- 4.7(e) `rem47e`: only a in T' (`ta : TT a`); no A c M(A), no a in C_I(a).
  `Mid a b` = b in OT, psi_I a <=' b <' I.
- 4.7(f) `rem47f`: z = `minT a d`; right side `RF A a z k c`.
- 4.7(g) `rem47g`: hypotheses packed as `GH b c` (b, c in OT, b~ <=' c,
  mI b = mI c); conclusion `Eqv (Cap (C b A) (suc (tilde b))) (Cap (C c A) ...)`.
- 4.9(e) `rem49e-phi`, `rem49e-om` (no extra hypothesis), `rem49e-sum` with
  `WDC (Cap A (tilde a))`. Parts hypothesis `Good A a p`.

Open (small, for 4.17(ii)): Def. 4.14(a)'s form of WD ("x, y in A") gives
`WDC (Cap A (tilde a))` once x <' cat x y and y <' cat x y are proved for
cat x y in OT (x, y /= 0). Not in OTF yet.

Mirror: `tools/otsec4.py ca47 5` (the proved (e) on 1,504,035 instances, (f)),
`ca49e` (29,959 instances), no failures.

Checker conventions learned (keep them):
- `fw P Q e`, `bw P Q e`, `ca-sup`, `ca-el`, `ca-sup-r`, `ca-el-r`: explicit.
- An implicit-argument match (`abF (trans (sym ..) ..)`, `subst`, `sym`,
  `trans`) in a declaration with a hypothesis "_ in C^a(A)" in scope opens
  the opaque C. Move the equality/contradiction into a named lemma with
  explicit arguments and no C in scope: `lt-abs`, `le-abs`, `irr-abs`,
  `at-OK`, `at-om`, `at-I`, `at-psi-*`, `nf-OK`.

Next: Section 4.3, W(A) (Assumption 4.10 = Def. 5.6, Lemma 4.13).
