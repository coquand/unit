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

## Step 1 in progress (points of a comprehension)

DESIGN.md "Interfaces of the encoding" states the design.  Presheaf has
SigE/SigT, pairE/fstE/sndE (+ fstE-pair, sndE-pair, pairE-eta, act-pair by
refl; pairE-snd, sndE-path, pairE-inj); TyL[G, B] has pr/pr1/pr2 (the same
at G, B); CLine.FT has lline/lover/lval/lnat (the line of an element of
AI; replaces .2.1/.2.2/.2.1.1/.2.1.2 on TL points).  The code is NOT
locked yet: the lock is `SigE = VC.SigO ..`, pairE/fstE/sndE through
pairO/fstO/sndO, and VCode's pairO/fstO/sndO made transparent (only SigO
stays opaque); checked on a scratch copy of core with that patch applied.
Migrated so far (they check with the lock): Presheaf, PresheafFormers,
PresheafPi, GPre, CPartial .. CHtpyOps in CBase order (CPartial CMove
CMoveLaws CGlueRC CSub COp COpMove CLine CConn CFillProb CFill CFillEnd
CLineSide CHornRetr CMapLine CCart CFillMove CFibSub CCartLaws CTrFib COpTr
COpLaws CCartLaws2 CFibExt CPath CPathProb CPathComp CPathFib CHtpyOps
CPathCart CPathNat CSig CPiE CPi CSigNat CPiCart CPiNat CEquiv CTr CTrOm
CTrB CTrP CTrE).
Next: CHFibCart, CHSub, CHFibLaws, ... in CBase order, then the instances,
L9, L9b, truncation; then lock (Presheaf + VCode as above) and measure.
Method per file: under the lock the checker reports each raw pair
("cannot infer a type for (x, b)") and projection ("not a pair: e : Idx
(VCode.SigO ..)"); rewrite them to M.pr S x b / M.pr1 S e / M.pr2 S e with
M the TyL module of the point and S its stage.  Hidden arguments for
fstE/sndE were tried and dropped: inference only works when the type is
literally SigT (fails through Pts K = SigT ..).

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
