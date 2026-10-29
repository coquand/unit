# Handoff: making core follow seg/WRITING.md (branch `core-abstraction`)

Goal: the formal proofs of core should follow what a mathematician writes,
with the abstractions a text would introduce.  Measured symptom (29 Oct
2026): core is 10x slower per declaration than sag/chatelet (2.1 ms vs
0.21 ms), opens 5x more definitions, and 58% of its openings are the
encoding (V.Idx/Ix/mkV/SigV ~30%, Presheaf, GPre.TyL, BC), against 93%
mathematical notions in Chatelet.  The headers and the step structure are
fine; the defects are one level below.

## Method (every step)
1. Informal first: a short section in core/DESIGN.md for the new notion and
   its characterising lemmas, before code.
2. Add the record/accessors and their refl lemmas next to the definition,
   migrate the users, lock (`opaque`) last; what fails after the lock are
   the hidden steps.
3. Measure: `./segc core changed` (0 failed), then
   `seg All.seg --opened` in core/ and compare per-file metrics.  The
   machine's speed varies: time the previous commit alternately
   (`git archive <rev> core | tar -x -C <scratch>`), never against an old
   number.
4. One commit per step on `core-abstraction`.

Lesson: state a recursion fact on the recursion (`Drec (suc m) = Dstep m
(Drec m)`, 0.00 s), not on a field (`(Drec (suc m)).R F = ...`, 4.5 s);
derive the field form by apH.

## Done (commits 60536d9 .. 24087f9)
- CPostRec: drecD by refl, Drec locked, DF face lemmas used downstream;
  CPostNat.EqR takes the two records (zeroEq/stepEq).
- CUaFull1: no second name for x.1.1; `mid` stated once.
- CIdEquivNat.sdEq as chains (EndKit.lv accessor in CLine, CCart.mS-val).
- Aliases removed: RES (8 files), CExt G'/EA/EA'/KBE, CPosEl1.yP.
- Copies removed: CCartLaws.CC/CG (use CCartLaws2), pair-eqV1 (one, top
  of CExtEq1), SigNat.coerce (now CwF.Formers.coerce), VCode duplicate
  names, CPath end0g/end1g (one endg).
- Result: 49.7 -> about 43 s at equal load; 18051 -> 17972 declarations.

## Step 1: stopped (points of a comprehension), 2026-10-29

Status: the barrier is NOT enabled in core; the migration is stopped.
Passing checkpoint: commit 96270b9, tag `abstraction-step1-stopped`
(full check 282 modules, 0 failed, 52.8 s).

What exists: Presheaf SigE/SigT, pairE/fstE/sndE with refl lemmas; TyL
pr/pr1/pr2 (+ pr-eqV); CLine.FT lline/lover/lval/lnat.  The intended lock
(SigE = VC.SigO, pairE/fstE/sndE through pairO/fstO/sndO, VCode leaving
only SigO opaque) was applied only to a scratch copy.  Under it, 21 files
(CLocHtpy, CLocEtaH, CLocUniv, CLocBound*, CTrunc*; about 170
declarations) still use raw points.

Measurement (identical migrated sources, barrier off vs on, segd --opened
--only M, alternating, 3 runs each; counts identical across runs):

| module       | opened        | encoding opened | time          |
|--------------|---------------|-----------------|---------------|
| CPath        | 5784 -> 5573  | 3292 -> 3092    | ~0.01 s both  |
| CLocDNUniv   | 7039 -> 7378  | 3780 -> 3999    | 3.0 s both    |
| CGlueCartNat | 68235 -> 65323| 17983 -> 15123  | 2.0 s both    |

No checking-time benefit; openings change by about 5% either way (SigV/mkV
saved, one extra layer through pairO).  Readability cost is large: every
projection names the point's type and stage, e.g. `v.1` becomes
`(TKD.pr1 W v)`, and in parameter telescopes without a local module name a
single declaration reaches about 600 characters (CGlueCartNat PtA).

Decision: stop.  Do not migrate the remaining files, and do not start
step 2 to recover readability lost here.  Revisit the barrier only for a
concrete need to change the point representation.

Limitation: the experiment isolates the barrier, not the accessor
migration against the original source.  Before carrying the mechanical
pr/pr1/pr2 rewrites elsewhere (or merging them), assess them separately;
a passing check does not show they improve the development.  The targeted
repairs (lval/lnat in place of .2.1.1 chains, pr-eqV in place of
pair-eqV/pair-eqV1, CLocD.evalE on whole points, explicit arguments where
inference had hidden a step) stand on their own.

## Plan (remaining)
1. Interface for points (largest effect).  Presheaf: extP.ob via SigT;
   pairE/fstE/sndE with refl lemmas (fstE-pair, sndE-pair, pairE-eta,
   act-pair), then lock; GPre.TyL points from them instead of W.Ix tuples
   (TyL already locks fromE/fromE-eq).  PresheafFormers: SigAB.o / IdAB.o
   on VCode's SigO / IdO, h/snd'/pair' with pairO/fstO/sndO.  Cat/CPosC:
   elLin n i h with car-lin / le-lin, then lock lin, mkOb; car/le accessors.
   Also BC vs idH/compH (CBase.seg:38): one name.  Migrate in All.seg order,
   lock when the tree is migrated.
2. Record `Cart[D, A', G, A]` (s, s-nat, ta, tapt, tanat, tainj, bk, bkta)
   with id, compose and their laws; "D and K_N preserve carts".  Consumers:
   CMove.Mv (21 params), CCart (12), CCartLaws2, CGlueCart / CGlueCartNat
   (51-arg telescope) / CGlueUniq (GU, GU2), CLocDCart, CCoskCart,
   CLocDUniv / CLocDNUniv (CC/CG, 1.1 s in Nat.nat), the 19 files with the
   identity cart spelled out (`\ X x u -> u, \ X x u -> refl ...`).
   Also: the classifier (Cl, clSub, clSub-id, clSub-o, encCl) as one
   structure (373 occurrences); PathFib passed whole (CIdEquiv.IE, CIdFib.IF).
3. Problems as records, naturality as apH: `Prob X` + prob-ext for
   CBoxFill.Compare; SqData / BoxData for CPostSqNat.SqZCmp/SqSCmp,
   CPostBox.BoxZCmp/BoxSCmp (then CPostHomNat.TopS.rd2, 0.6 s, goes);
   faces of [m] as a sieve (CPostBdry defines sides only for m = m'+1, which
   forces Z/Step copies in CPostNat, CPostHomNat, CPostInvNat, CPostSq,
   CPostBox); CPostInv's stage convention in CPostRec (no junk stages);
   SqS as BoxS at Y = [1]; E2.HT / E3.HT and DR / DRK as one.
4. Generic statements for parallel developments: one former of compatible
   families (CLocD.DT, CCosk.KT, CLocDNC.CEl; cart preservation CLocDCart =
   CCoskCart); CUaD = CFibU1 and CUaN = CFibU2 ("same construction");
   CLocDUniv / CLocDNUniv; CTruncIsProp.Connect = CLocBoundContr.Connect;
   CGlueUniq GU2 telescope; CFill / CPathComp n-sided composite;
   CFillMove / CPathNat sd-eq; CExtEq2 CompatA/CompatB; CUaFull1.ChG vs
   CExtEq2.Ch (generalise Ch to a local point).
5. Headers for CTrunc* and thin CPost* files; the two truncations
   (CTruncProp.IsPropE vs CTruncIsProp/CTruncHProp) related or merged;
   unit.tex table and DESIGN.md updated.

Open questions for the user: the 23 citations of `postnikov.tex` (it is
seg/notes/postnikov.tex; some labels, e.g. Theorem conv, Corollary fib,
have no counterpart in doc/postnikov-limit.tex).  Presheaf.p-lift-P /
p-sec-P duplicate CwF.p-lift-T but are needed to build the CwF instance
(left; small cost).

Smaller items seen but not done: CTruncFill `m = suc k` alias, CPostBdry
`BG.m`, `X : Ob = H.X` re-declared (CLocHorn, CCoskHorn, CBoxHorn), CPiNat /
CPiCart / CSigNat / PresheafPi `A' = subTy ...` re-declaration chains,
CLocDNC.rdId-act' instance written 20 times, projection chains `.2.1.1`
(about 1100; use EndKit.lv), CFibU2's own RES = D.GIU.
