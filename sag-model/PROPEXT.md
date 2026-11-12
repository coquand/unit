# PROPEXT: propositional extensionality at the poset base

STATE (2026-11-12, paused at the user's request): **none of the five files
is written.** FibUaGm, FibUaHm, FibUaHk, FibUaC0, FibPropExt: not started.
No .seg file was created or edited; the shared tree is unchanged apart
from this note.

NEXT STEP: write FibUaGm (the map g), design below.

## Goal

An element pe : PU.PropExtTy for the CwF that cobar uses:
FibCwF[a, a+] with FibId[a, a+].fibId and FibUniv[a].fibUniv, at level a++.
The top-level instantiation will pass FibPropExt.pe. The pe parameters of
the other sessions' files stay as they are.

## The chain, checked (2026-11-12, ./segc sag/cobar check, 7 modules, 3.5 s)

uaC0 : El U0 UaW.UaC0
  -> CwFUaW.UaW[a++, FibCwF.., FibNF[a, a+].nf, FibUniv[a].fibUniv].W[uaC0].uaStr
  -> CwFPropExt.PropExt[a++, .., UA].propExt : PU.PropExtTy.
FibUaF already instantiates UaW with FibNF[a, a+].nf, so NF's type matches
(this has to be checked again in FibPropExt). Only uaC0 is missing.

## The plan for uaC0 (M1.md "Step 3, S4", checkpoint of 2026-11-10)

Files in sag-model/, each with a symlink in sag/cobar/.

1. FibUaGm: g : NMap[U0, UaTy', Q0.1].
   - A point of extP U0 UaTy' at X is (x, D') with D' : UaT0 X F, that is
     (D'.1 : GD1 X, (D'.1.1 = F, full)).
   - ell (x, D') = (D'.1, D'.2.2) : R = UB.CU.resCtx, a PSub. Its naturality
     needs the fullness proofs to agree, which holds because IsT is a
     proposition.
   - m : PMap[U0, UaTy', Q0.1], with mE = the point of T3 given by
     Phi3 (ell v), read as a point of U0.Q0. Pairs are definitional:
     Presheaf.pairE-eta is refl, and tel/telAct are refl.
   - mpt: zx (Phi3 w) = x, from FibUaPhi.PhiX and D'.2.1, on U0 = 1.Cod
     points (tt, code).
   - mnat: Phi3's naturality.
   - g.nfun X x D' = BodyOf[U0, UaTy', Q0.1, m].body.eob X (x, D'), and
     nnat comes from body.enat.
2. FibUaHm (split it if it nears the cap): (H-map) the b and r parts of g∘f
   are those of the point. Hb uses PhiB and uAct-id. Hr uses
   FibUaHr.RT.H.Hr carried through FibUaPhi.Pr along fh, then the
   body-to-Pi step (fun-inv, el-ext).
3. FibUaHk: the k parts agree by CwFCC.eqC/piCC, since Kr r is contractible
   once it is inhabited. Pair this with the strict (b, r) part to get an
   element w : Id(alP, q) of Q0[p] over U0.Q0. FibHt.YH turns it into
   H : HT[U0, Q0.1, Q0.1, compN f g, idN].
   - YH only asks for alP pointwise equal to (g∘f).nfun (alQ). So alP may
     be the internally built pair (b, (r, k'')), and its comparison with
     g∘f stays pointwise.
4. FibUaC0:
   - ua' = CPosFinal.ua moved along FibUaF.pim (CFibSub cart / moveContr).
   - CLocBoundRetr.Relative[U0, Q0.1, UaTy', f, g, ua'].extension.
   - Correct[U0, Q0.1, compN f g, that, H, Q0.2.1].extension : ContrOp on
     Q0 (the pattern of FibHt.CF).
   - FibContr gives El U0 (isContr Q0). Check that FibUaF.Q0 is
     definitionally the Sigma inside UaW.UaC0 (QV.FYX, QV.K1).
5. FibPropExt: UA and pe as above, about 20-30 lines.

Estimate: ~450-650 lines; file 2 carries the risk (transport bookkeeping,
10 s per file at FibCwF).

## Facts found while reading (useful for file 1)

- CPartial.PMap: mE on SigT, mpt on the first component, mnat. BodyOf
  (FibUaG) turns a PMap into an element of A[p] over D.B.
- CHtpyOps.NMap: nfun, nnat; compN, idN; HT[G,A,B,al,be].PT.PathP.
- CUa.UaU: UaT0 X F = (D : GD1 X) * (Id D.1.1 F * IsT (allS X D.1.2.1)).
  uaTact acts by GD1Ctx.act and fullAct; uaExt says that the GD1 part
  determines the point.
- FibHt.CF.contrOp is the template for the Correct step: c = T.2.1.
