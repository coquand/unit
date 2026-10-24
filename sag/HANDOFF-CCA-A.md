# Worker A: Scott continuity, Barton–Commelin, the interval (CCA.pdf)

Read first: `sag/CCA-DESIGN.md` (scope, split, representation choices, rules),
`sag/CCA-INTERFACE.md`, `CCA.pdf` §2 and §3.4 and Appendix C, and `stone/DESIGN.md`
§6 for what SSD already gives.  You own `sag/cca/` only.  Worker B works in
`sag/em/` and `sag/ccacoh/` at the same time.  Do not commit.

## Steps

- **A0. Skeleton.** `cca/All.seg` like `stone/All.seg`: symlinks to the
  foundation (`pn/`), to `stoneseq/` (colimits, ODisc, choice) and to the
  `stone/` files you need (up to `Thm418`, `Lemma412`).  Check that it
  loads: `./segc sag/cca changed` from the `unit` root.
- **A1. §2.1–2.3, Scott continuity for Stone spaces.**
  - Lemma 2.1.6 (an increasing open cover of a Stone space is eventually
    everything): local choice + boundedness (SSD Lemma 3.6, i.e. the
    bound in `stone/Cor37` / `Compact.finite-subcover`).
  - Lemma 2.1.7 (towers of inhabited families) from `stone/Remark34.SurjLim`
    (Remark 3.4 for surjections) and Cor. 3.12.  B's `stoneseq/Lemma59Stone`
    / `FibreSeq` already does most of it for Lemma 5.8: reuse, do not copy.
  - Lemmas 2.3.3, 2.3.4, Prop. 2.3.5 (colim of Π x : S, Iᵢ(x) = Π x : S,
    colim Iᵢ(x)).
  - Lemma 2.3.6, Prop. 2.3.7 (colim (Sₖ -> I) = (lim Sₖ -> I) for I overtly
    discrete).  `stone/Cor37` is the case I = N, with the compactness lemma
    `Vanish`: generalise rather than redo.
  - Lemma 2.3.8, Prop. 2.3.9 (Tychonov's dual), Def. 2.3.10, Thm 2.3.11.
  - **Announce Props 2.3.5, 2.3.7, 2.3.9 and Lemma 2.1.7 as stable in
    `CCA-INTERFACE.md` as soon as they check: B needs them.**
- **A2. The interval** (`CCA-DESIGN.md` §4): I as a quotient of 2^N by the
  closed relation built from dyadic csₙ; I is compact Hausdorff (needs
  quotients of compact Hausdorff spaces by closed equivalence relations,
  CCA Prop. 2.4.3 (iii)); I∼ₙ^k (Def. 3.4.2) and
  Σ x : I. (cs⁻¹ x)^(k+1) = lim I∼ₙ^k; Lemma 3.4.1 (maps from I to a finite
  set are constant), Thm 3.4.3 (i) (maps from I to an overtly discrete set
  are constant; needs Thm 2.4.6 or Prop. 2.3.7 through cs), Lemma C.0.5.
- **A3. §2.4.** Lemma 2.4.2, Props 2.4.3–2.4.5 (Tychonov and its dual for
  compact Hausdorff spaces), Thm 2.4.6.
- **A4. After the join with B.** Thm 3.4.3 (ii) (from B's Prop. 3.1.8),
  (iii) (from B's Thm 3.3.2 and Lemma C.0.6, Eilenberg–Steenrod VI.6.10 for
  the interval complex: decide with the user whether to prove it or state
  the needed exactness directly), Lemma 3.4.4 (i), (ii), (iii).

Done when each step checks under `./segc sag/cca changed`, every file < 10 s,
and a `cca/README.md` lists what is proved with CCA numbering.

## Progress (2026-10-24)

- A0 done: `cca/All.seg` = the `stoneseq/All.seg` tree (links) + the cca
  files; full check 115 modules, 0 failed, 1.3 s.
- A1 done (see `cca/README.md` for the table): Lemmas 2.1.5, 2.1.6, 2.1.7,
  Prop. 2.1.4 (i)-(v), Lemma 2.3.4, Props 2.3.5, 2.3.7, 2.3.9, Lemmas 2.3.6,
  2.3.8, Def. 2.3.10, Thm 2.3.11, all for towers of Stone spaces.
  Announced in `CCA-INTERFACE.md`.
- `--opened`: every declaration of the cca files opens at most 84
  definitions (`CountableProduct.NotAll.W.index`; all others <= 25); every
  file < 0.15 s.
- A2 done: `Interval` (I = 2^N/~, closed, effective quotient, compact
  Hausdorff directly: Prop. 2.4.3 (iii) is not needed for I),
  `Lemma341` (Lemma 3.4.1, Thm 3.4.3 (i), by one descent lemma), `Dyadic`
  (vertices, Def. 3.4.2 tuples), `Def342` (the limit identification),
  `LemmaC05`.  Full check 121 modules, 1.4 s; max 22 openings.
- A3 done: `Prop243` (Lemma 2.4.2, Prop. 2.4.3), `Prop244` (Tychonov),
  `Prop245` (Tychonov's dual for CHaus), `Thm246` (Scott continuity for
  C_CHaus).  `Thm2311.Pis` now takes an `FTower` (no hypotheses;
  `fam T` forgets a `CTower`), so that Thm 2.4.6 reuses it for compact
  Hausdorff towers; `Prop239.Lemma238` is now an instance of
  `Descent238` (same name and result).
- A4 partly done: `Thm343ii` (Thm 3.4.3 (ii), through B's
  `H1Stone.Prop318.backward`), `Lemma344` (Lemma 3.4.4 (i), (ii)).
- Next (A5, with Thm 3.3.2 in B's form (C), CCA-DESIGN §5): Ȟ¹(I, T, B) = 0
  for every family B of overtly discrete (abelian) groups over I
  (T x = cs^-1 x), generalising `Thm343ii` from a constant G.  Plan:
  local choice gives a Stone cover with presentations of B by stages
  Fin (c_t n); by SSD Cor. 3.7 the c_t n and the transition maps factor
  through finite stages, so the coefficients form a tower in C_Stone and
  Thm 2.3.11 applies; then the argument of `Thm343ii` (Def. 3.4.2,
  Lemma C.0.5) and descent along the cover as in `Prop239`.  A general
  lemma "an overtly discrete family over a Stone space comes from the
  stages" is the by-product.  Fallback if this is much harder: form (B)
  and a direct proof of Lemma C.0.6.  Then Thm 3.4.3 (iii) (from B's
  Thm 3.3.2) and Lemma 3.4.4 (iii) (with B's K(A, n)).
- **A5 is FALSE (2026-10-24, found before any code).**  Ȟ¹(I, T, B) = 0
  fails for some family B of overtly discrete abelian groups over I.
  Counterexample: A = Z (or Bool with xor), U x = (x /= 0) and (x /= 1) (open:
  I is compact Hausdorff, so x = 0 is closed and its negation is open),
  B x = {a : A | a = 0 or U x} (an open subtype of A, so overtly discrete).
  P x = {a : A | (x = 0 -> a = 0) and (x = 1 -> a = 1)} is a B-torsor:
  inhabited via cs (y_0 = 0 gives cs y /= 1, take 0; y_0 = 1 gives cs y /= 0,
  take 1), and a' - a in B x (decide a = a'; if not, x /= 0 and x /= 1).
  A section of P is a map I -> A with value 0 at 0 and 1 at 1, which
  Thm 3.4.3 (i) rules out.  So H¹(I, B) /= 0, and by Prop. 3.1.8 Ȟ¹(I, T, B) /= 0.
  (Semantically B = j_! A for j : (0,1) -> [0,1], and H¹ = A.)  So the
  hypothesis of B's `Thm332.Hyp` cannot hold for X = I.  The paper's route
  only needs constant A: Thm 3.3.2 degree by degree (form (B)) plus
  Lemma C.0.6.
- Decision (user): route (C′).  B: the Čech dimension shift in vanishing
  form and "Ȟⁿ(X, S, A) = 0 for all n >= 1 gives Hⁿ(X, A) = 0 for all n
  >= 1", on A's `Cochains.Cech`.  A: Lemma C.0.6 and Ȟⁿ(I, T, A) = 0.
- Done: `Cochains` (ordered cochains, delta by recursion on the first
  point, delta delta = 0, cone, locality, naturality, `Cech`), `LemmaC06`
  (Lemma C.0.6, all lengths, by induction on the top vertex: no
  Eilenberg–Steenrod), `CechI` (`cech-I`: Ȟᵏ(I, T, A) = 0 for every k).
  All < 0.06 s; largest openings 56 (`CechI...Later.bound`).
- Done: `Thm343iii` (Thm 3.4.3 (iii): B's `Thm332C.thm332` on cs with
  `\ m -> cech-I Gr oA (suc m)`), `Lemma344iii` (Lemma 3.4.4 (iii),
  `em-local`, induction on m: identity types merely K(A, m) by
  connectedness and univalence, maps merely constant by (iii)).
  `Lemma344` refactored: the embedding+onto argument is the general
  `ByIds`, (ii) its instance (names `isLocal`, `odisc-local`, `bg-local`
  unchanged).  B's em/ and ccacoh/ files up to `Thm332C` linked.
  Full check 165 modules, 0 failed, 2.3 s; new files < 0.04 s, openings
  <= 19.  A's part of CCA is complete.
- Left: nothing in scope (Prop. 3.4.5 is out of scope).
- Done (2026-10-24, after the join): Lemma 2.3.3 and Lemma 2.3.4 as
  stated (`Lemma233`, 0.04 s, at most 8 definitions opened per
  declaration); delta = the alternating sum of Def. 3.3.1
  (`Cochains.AltSum`, appended, existing declarations untouched, max 12
  openings).  Cold full checks: cca 166 modules 2.35 s, em 50 modules
  0.29 s, ccacoh 149 modules 1.71 s, 0 failed.  No declaration opens more
  than ~500 definitions.
- Full check 133 modules, 1.5 s; largest openings 84
  (`CountableProduct.NotAll.W.index`), all others <= 30.

Representation notes.
- `Prop235.Tower[S]` is a sequence `at x : Seq` per point (not two
  families): the checker has no eta for records, and the constant tower
  must be literally `\ x -> J` so that its colimit is `Colim[J]`.
- `Lemma236.FMaps` is the F-valued generalisation of `stone/Cor37.Maps`
  (N-valued, read-only, not refactored).  `Lemma236` (finite towers, via
  SSD Cor. 3.7) is kept; `Lemma236Stone` is the general case and
  `Prop237.Scott237` uses it.
- Index arithmetic is avoided by proving stage-0 statements and shifting
  the tower (`Lemma236Stone.Shift`, `Thm2311.shift`/`Shifted`): S (d + 0)
  is not S d definitionally.
- `AffineHLevels` (pn/) is linked for `EquivalenceProofs.proposition`
  (isEquiv is a proposition).
- `fails` is a keyword of the parser.

## Openings (totals, 2026-10-24)

Measured as the TOTAL of the `*k` counts on each `--opened` line (rule 6
of seg/WRITING.md; earlier reports in this file gave distinct counts).
Script: sum the counts per declaration (`--opened` piped through awk).
Changes made after measuring:
- `fe` (funext from univalence) is `opaque` in em/, ccacoh/, cca/All.seg:
  funext is used through happly-funext / funext-happly only; checking
  computed through FunExtUA.FE (48 openings in LES.over1).  All three
  trees check unchanged, em 0.81 s -> 0.58 s.
- LES: the aliases m1 = suc n, m2 = suc (suc n) removed (opened 700 times
  each in LES.over1: one name per notion); psi^-1 typed with Puppe's names.
- PiPt: `happly-loop` stated generically (`Pi.PiLoopAt`, components named
  F1, F2, Fy, h-pt, h-ap), PiLoop an instance: 2025 -> 334; `pi-comp`
  through the component lemma `Pi.PiComp` (maps and pointings given
  separately, no projections of pointed maps): 1187 -> 117.
- ScottCech.staged: the stage cocycle named once (`Pick`): 1095 -> < 260.
- One name per notion (canonicity-69, after milestone 1): the type
  abbreviations of the generic modules were aliases of named types and are
  inlined (Puppe.F/fp/OB/g/G/gp, GEX.F/fp/OE/OF/OF', Puppe2.OE/FD/fd,
  PiFib.PF/FP/fP/Fx/fx, PiLoopAt.PF), and LES writes Eps.P for the products:
  LES.over1 689 -> 433, LES.fst3 520 -> 418.
Remaining (none above 504):
- LES.sq2 504, Gover 437, over1 433, fst3 418: Eps.P / Eps.pP opened
  about 200-290 times each, i.e. B's named products (Eps.P m = (x : X) ->
  K(B x, m), pP) against the Π-types that the generic PiMap / PiFib
  produce.  Removing this means stating Eps through PiMap (or the
  reverse): to do in the pass over B's Eps after item 8.
- EpsEv.Step.loops 572: KK.OK / Maps.OB, the same class; same pass.
All other declarations of this session: <= 494 (PiOne.Induced.hom).

## Openings pass after item 8 (2026-10-24, totals)

**Rule (WRITING.md rule 2, measured):** each written instance M[a, b] is a
new expression whose arguments are checked where it is written; name it
once (`module KA = K[A', oA']`) and use the name.  Thm332A.on-delta wrote
K[A', oA'].CK.f3 several times and re-checked Coker's 20 arguments each
time (1622 -> 491 after naming f3 in K).

Rounds (ii), (i), (iii), all committed or ready, 0 failed:
- (ii) Thm332A: f3, f3-d, iso named in K; base split into base-iso and
  base-nat; CechH0's alias H0 removed.  on-delta 1622 -> 491, base 630 ->
  311 + 277.
- (i) Eps, EMMaps: on loops conj 0 is c0 = unband o h o band (resp. psi^-1 o
  band), named, with c0-conj by refl and c0-mult stated in EM1 names (K1,
  k0); accessors for ps, eA, LD0 in Diag.DStep.  Eps.mult0 1362 -> 240 (+
  c0-mult 490), KMap.mult0 970 -> 382, DStep.LD 671 -> 468.
- (iii) LES: Pp (suc (suc n)) for the 63 written PiMap's (sq2 504 -> < 290);
  LESNat.natural: loop types as Id, not PiOne.O (635 -> 454); CechNat:
  named instances QA2, QC1, MCq, natural split into Goal / on-cl / natural
  (574 -> on-cl 513: the rest is Snake's cocycle names against CechGrp's).

Changes (all trees check; em 1.61 s, ccacoh 3.95 s, cca 2.54 s cold):
- inlined the type aliases of FibSeq.SES.Obj (X0 x0 .. OC oc) and of
  Eps.Diag.DStep (X0 .. OZ oz), KK.OK (everywhere: em, cca/Lemma344iii) and
  DeloopMaps.Maps.OA / OB (in Maps and at the uses in Fibres, LoopCalc);
- accessors for the parts of pointed maps in FibMap (ff f0 ff' f0' fu u0
  fv v0) and LiftUnique (ff f0 m1 m2, mm).

| declaration | before | after |
|---|---|---|
| FibSeq.SES.NullStep.chain | 1333 | 475 |
| FibSeq.SES.Step.u1 | 842 | 436 |
| FibSeq.SES.Step.sq | 680 | 226 |
| Eps.Diag.DStep.chain | 1065 | 442 |
| Eps.Diag.DStep.LD | 874 | 671 |
| Eps.Eps.mult0 | 1576 | 1362 |
| EMMaps.KMap.mult0 | 1201 | 970 |
| EpsEv.Step.loops | 572 | 435 |
| FibMap.dd-nat | 819 | 271 |
| LESNat.natural | 731 | 635 |
| LiftUnique.snd-eq | 569 | 404 |
| CechNat.natural | 574 | 574 |
| LES.sq2 | 504 | 504 |
| Thm325...FromCover.result (B) | 722 | 722 |
| Thm332A.base | 630 | 630 |
| Thm332A.Step.NatAt.on-delta | 1622 | 1614 |

Remaining causes: the two mult0 open KK.pt / KK.K against EM.EMSpace.pt /
K (KK is a reindexing layer over EMSpace, and the band lemmas are typed in
EM1/TrivialGerbe terms): fixing needs KK restated without the layer.
Thm332A: Thm332's own onto : Surjective q against T.Sx (B's code mixes
them; Sx, Surjective, Fibre about 100 each), E / L against Thm332.Cov.AS
and T.CX[..].C2, and the group record layers (QGrp.grp, Quot.Q).
LESNat.natural, CechNat.natural, LES.sq2: π₁ names (PiOne.O against Id)
and Eps.P against the Π-types of PiMap.

## Gaps

(Log here every statement of the paper used without proof, omitted
verification, broken reference, or citation replaced by a proof.)

- Lemma 2.1.6 assumes the U i open; the proof (local choice +
  boundedness) does not use it.  Hence Lemma 2.3.3 (images are open) is
  not needed for Prop. 2.3.5; it is formalised separately
  (`Lemma233.lemma233`, via SSD Lemmas 2.6-2.8).
- Prop. 2.3.5 holds for towers of sets; overt discreteness is not used.
- Lemma 2.3.4: Prop. 2.3.5 uses the form "a phi in the image of stage j
  lifts to a later stage" (`Prop235...Lemma234`); the statement as a
  surjection of colimits is `Lemma233.lemma234`, derived from it (the
  forgetful map from the colimit of the image tower is injective).  Only
  that the I i x are sets is used.
- Lemmas 2.3.6 and Prop. 2.3.7 "omit the verification that this is the
  canonical map": the formal proofs work with the canonical map directly
  (injective + surjective), not with the chain of equivalences.  So far
  only for towers of finite sets (Lemma 2.3.6 then follows from SSD
  Cor. 3.7, without Stone duality for colimits of algebras).
- Prop. 2.3.9: local choice applies to families in U l, but presentations
  are large; the proof uses presentations by stages Fin (c n)
  (`Prop239.FinPres`), merely available by countable choice.  The paper
  partitions T by the values of the bounded l_k; the formal proof
  partitions by the fibres of T -> E K through which c factors (SSD
  Cor. 3.7), which needs no bound.
- Prop. 2.1.4 (iii) is proved without colimits of Boolean algebras: a
  countable product of Stone spaces is Stone (presentations by countable
  choice, Cantor pairing made an equivalence in `CountableProduct`), and a
  limit is a closed subset of it.
- Lemma 2.3.6 for towers of Stone spaces is proved without Stone duality
  for colimits: injectivity by compactness (a limit of inhabited Stone
  spaces is inhabited, `LimInhabited`, from SSD Lemma 4.5) and Lemma
  2.1.6; surjectivity for 2-valued maps by separation (SSD Lemma 3.16),
  then for finite B through the characteristic maps.
- Thm 2.3.11 "omits the verification": the formal proof is pointwise
  (injective + surjective), by Ext(N) and Extension(i) on shifted towers;
  only Props 2.3.5, 2.3.7 and Lemma 2.1.6 are used, not the chain of
  equivalences of the paper.
- Thm 3.4.3 (i) uses Prop. 2.3.7 through cs (the paper's second option),
  not Thm 2.4.6; Lemma 3.4.1 and 3.4.3 (i) share one descent lemma
  (`Lemma341.Descent`): v 1 0 0 .. ~ v 0 1 1 ...
- Lemma C.0.5 is stated with the vertices V n = {j < 2^n} (numerators) and
  near pairs as dependent arguments, with worker B's conventions for
  cocycles (`em/CechNA`): d a1 a2 . d a0 a1 = d a0 a2,
  g a1 . d a0 a1 = g a0.  Exactness at G^(I~^1) builds g by recursion on
  the numerator (the paper's beta).
- Thm 2.4.6: the paper's proof identifies subtypes of colimits ("Q_j");
  the formal proof is pointwise: injectivity by pulling back along the
  Stone covers of Lemma 2.4.2 (pullback of sections injective, colimits
  at z and at y = lim p z identified up to transport), surjectivity by
  Thm 2.3.11 (injective) for the Stone tower of pairs {p s = p s'} and
  descent of the shifted section.
- Prop. 2.4.3 (iii) is not used for the interval: I = 2^N/~ is compact
  Hausdorff directly (`Interval.Over.chaus`).
- Lemma C.0.6: the paper cites Eilenberg–Steenrod VI.6.10 (ordered vs
  alternating complex); replaced by a direct proof (cone at the new
  vertex, gluing along {j, j+1}).  The formal differential is the
  recursion delta phi (v . t) = phi t - delta (phi_v) t, equal to the
  paper's alternating sum (`Cochains.AltSum.alt-delta`; nothing else
  uses the sum).
- Thm 3.4.3 (iii) as planned (form (C), Ȟ¹ for all families) is false:
  see A5 above.  The paper's own route only needs constant coefficients.
- Lemma 3.4.4 (ii): the paper's "identity types in BG are G-torsors" is
  used as: X = Y is the set of equivariant maps (em/FundThm with
  GTor.contr), whose carrier is overtly discrete pointwise.
