# seg/core — the generic core, rebuilt

The mathematical specification is seg/notes/model.tex; this file maps it
to layers and files (section numbers refer to model.tex).

seg/model is the finished, checked proof and the quarry: proofs are copied
from it, but every *statement* below follows this design.  No lists of
faces anywhere; one notion of contractibility; every structure defined once
on universal data and obtained by substitution along a classifying map.

## L0  Metatheory (quarry: Base, Prelude, Paths, Axioms, Trees, Arith, Sum, V, VCode, Encode, SmallCat, Presheaf, Cat)

Copied unchanged: iterative sets V (codes are compared by strict equality in
V, never up to iso), funext and univalence as parameters of one segment,
`lem` only in a Classical segment (Δ).  Presheaves on a small category:
`PCtx`, `PTy`, `PSub`, `subTy`, `mkTy`, `extP`, `ty-ext`.

## L1  Base: a category with an interval and canonical sieves (model.tex §2) (quarry: IvBase, CSieve, PosS, DeltaBase)

Parameters: a small category, an object [1] with points e0, e1 (I = y[1]),
constant maps, connections.  `Phi X` is an abstract presheaf of sieves on X:
`Lands W X Q f` (a proposition, closed under precomposition), `pre`,
`phi-ext`, `allS` (decided at the identity), `emptyS`, `topS`, the points of [1]
(`ptS`), **union** `bigU` of finitely many sieves, and **∀ along I**:
`forallS X L : Phi X` for a line of sieves L (a sieve of y X × I), with
`Lands f (forallS L) ⟺ L holds at every (f g , j)`.
Statement: one sieve per cofibration; a "list of faces" is only notation
for its union.

## L2  Partial elements and relative contractibility (model.tex §3) (quarry: GPre, GCofib, GCofOne, GContrMove, GFillS/X/XS, GTransfer*, GTransferEq*)

- A partial element of S over G at x : G(X) is ONE sieve Q with a section
  over it (`Side`).  Restriction along h is `rside`.
- **Relative contractibility structure** `RC(G, S, T, m)`, m : S → T over G:
  for each side, an extension in T at x agreeing with m on the sieve,
  uniform under restriction.  `ContrOp = RC(G, C, C, id)`; line composition
  `CompAt = RC(TV, TS, TV', endL)`; fillers `FibAt`/`TrivFib` and
  equivalence structures `EquivOp` (contractible homotopy fibres) are
  ContrOps on derived types.  Horn filling (Δ) is the special case where
  the sieve is the horn.
- `rc-ext`: two structures with equal extensions are equal.
- **Move** (one lemma, Construction "move"): along a map of contexts
  s : G → G0 (any levels), maps of totals S → S0, T → T0 over s (σ, τ),
  τ a bijection on fibres (injective over equal points, with a lift back),
  τ m = m0 σ; RC on the target gives RC on the source.  Laws, once:
  identity, composite, congruence; substitution is Move with identity
  fibre maps, so its laws are the composite law.
- **Operations without uniformity** (`Op`: extension + sides, as Δ's horn
  filling): RC = Op + uniformity; Move is stated for Op and lifted to RC.  This
  replaces GTransfer / TrF / TrEq and their law files, GSmallFib's
  transfer, DeltaClassifier.Sub and GFillX.
No ESI/KESI: they were statements about presentations.

## L3  Fibrations (model.tex §4) (quarry: GLine, GFam, GFill, GFillFib, GFibE, GSubst, GFibLaws, GHornRetr*, GPi*, GSig, GPath*, GEquiv*)

Path structure along I, line composition (`CompAt`, both directions),
fibrations `FibEL G = Σ A, Comp A`, fillers from compositions with
connections, substitution of fibrations (an instance of Move), Π, Σ, Path,
equivalences and their substitution.

## L4  Small types and the universe (model.tex §5) (quarry: GSmall, GSmallFib, GSmallFibI, GUniv, GUnivL, GElC, GYon, Encode)

`SPTy[G]` small types over a large context, `up`, `XSub`, `xsub`, `xsub-o`
(once for all small types).  The universe at a classifier `Cl`: codes `U0`,
`UCtx`, El as an `SPTy[UCtx]`; El along a code map *is* `xsub`.  El's
structures (composition, fillers) are given once on El and moved along
classifying maps by Move.

## L5  Glue data and Ext, Theorem 7 once (model.tex §6) (quarry: GGlueD, GGlueE, GExt*, GExtComp*, GExtEquiv*, GExtBig, GExtCmp, GExtSmall, GExtFibU, GXsubEq)

The presheaf GD of glue data at stage I: (A , ψ : Phi I , B on ψ , α ,
equivalence structure).  Ext of the universal data (`ExtBig`) with its
composition and its equivalence structure (Theorem 7) proved once; the
small copy SA (fibrewise comparison); for data α over Γ,
`Ext(α) = xsub ℓ_α SA`, its fibration by Move; naturality is `xsub-o` plus
the one data equation ℓ_{α[s]} = ℓ_α ∘ s.

## L6  Univalence (model.tex §7.1) (quarry: GUaPt, GUaPtNat, GUaUniv, GUaKfull, GUaOpN, GUaFull*, GUaLoc*, GUaGlue*, GYonEq*, GUnivEq, GCofOne)

`ua : ContrOp` on Σ (X : U) Equiv(X, A), defined on one side by the
universal datum U = (SA, AU, α, e) substituted along the Yoneda map of the
side's glue point.  Classifier inputs: `smallCl` (the code of SA along a
map) = the universal operation (composition for posets, horn filling for
Δ) moved along it; `smallCl-sub` = Move's composite law; `smallCl-full`
at full points (classifier-independent part shared).

## L7  The universe is fibrant (model.tex §7.2) (quarry: GCompU1-5, GTE*)

Comp(1, U) from ua (G7); `FibU.fibU : FibEL G` for U, without ESI.

## L8  Instances (model.tex §8) (quarry: PosS, Constr, PosetConn, PElL*, PElYon*, PUaOp, PCompU; DeltaBase, DeltaForall, DeltaClassifier, DElHorn, DGlueCl, DSmallCl, DSmallFull*, DeltaElFib, DUaOp, DFibU, Classical)

Posets: canonical sieves (PosS), ∀ via the cylinder object, the poset
classifier U_L.  Δ: canonical sieves, ∀ via prism covers, horn
classifier, El's horn filling (classical only through `lem`).  Final
statements as today: Theorem 7, `ua` as a ContrOp, `FibU.fibU`, for both.

## Status (2026-10-17, final)

Every result of seg/notes/model.tex is formalised in seg/core; the one
exception is the Yoneda remark of §6.2 (glue data as componentwise data),
which the text marks as not needed.  `./segc core all`: 178 modules,
0 failed, 38 s cold, every file < 4 s.  lem is used at exactly one place,
CDeltaHornBox.decDeg (the Delta statements sit inside CClassical.Cl).
Line counts and timings against seg/model: COMPARISON.md.

Files per section of model.tex:

- §1 Metatheory (L0): Base, Prelude, Paths, Axioms, Trees, Arith, Sum, V,
  VCode, VLift, Encode, SmallCat, Presheaf, PresheafFormers, PresheafPi,
  CwF, GPre, GYon.
- §2 Base (L1): CBase, CSieve.
- §3 Relative contractibility (L2): CPartial, CMove, CMoveLaws, CSub, COp,
  COpMove.
- §4 Fibrations (L3): CLine, CConn, CFillProb, CFill, CFillMove (filling
  commutes with moves), CCart, CCartLaws2, CFibSub, CPath, CEquiv; Thm
  "type formers": Sigma CSig, Pi CPiE + CPi, Path CPathProb + CPathComp +
  CPathFib; homotopies (CHtpyOps: HT, whiskering, retargeting, the
  constant homotopy, inverse and concatenation into a type with a
  composition, by CPathComp along a line of G.A.B; HEq); naturality
  (moves along carts over s): CSigNat, CPiCart +
  CPiNat, CPathCart + CPathNat; transport is an equivalence: CTr, CTrOm,
  CTrB, CTrP, CTrE.
- §5 Small types, universe (L4): CSmall, CUniv, CElC.
- §6 Gluing, Theorem 7 (L5): CCof, CExt-CExt4, CExtEquiv-3, CExtComp1-4,
  CThm7, CExtFull, CLineSide, CMapLine, CHFibCart, CHFibLaws, CTrEq, CEnc;
  universal glue data: CGlueD, CGlueE, CGlueLaws, CGlueRC, CExtBig, CExtU,
  CExtEq1-2, CExtFibU, CExtCmp, CExtSmall; glue data over a context are
  maps l : D -> GD (Voevodsky's form): CExtL (def:ext-ell, lem:ext-cmp),
  CExt7Nat (thm:7-nat, in move form).
- §7 Univalence and Comp(1, U) (L6, L7): CHSub, CUa, CGlueCart,
  CGlueCartNat, CUaD, CUaB, CUaN, CUaBN, CGlueUniq, CUaFull1, CExtFullCart,
  CUaSA, CUaSB, CUaOp; CFibU1-3.
- §8.1 Posets (L8): Cat, CPosC, CPosBase, CPosInst, CPosEl1-5, CPosFinal;
  generic for Cl = Fib: CFibCl, CFibExt, CCartLaws, CSmallSub, CFillEnd,
  CExtFullFib, CTrFib, CYonCart, CSmallFull1-3, CFibFinal.
- §8.2 Simplicial sets (L8): CDeltaBase, CSimp, CDeltaNat, CDeltaFact,
  CDeltaCl, CBoxHorn, CDeltaRetr, CDGlue-CDNormE (and the CD* stages),
  CClassical, CDeltaHornBox, CDeltaHornToFib, CDElHorn, CDeltaElFib,
  CDGlueCl, CDSmallCl, CDSmallFull, CDSmallFull2, CDOpFull, CDOpYon,
  CDeltaFinal; generic for filling operations: COpCl, COpTr, COpLaws,
  CHornRetr.

- §9 Identity types (L3, L8; 2026-10-17, seg-62): Swan's Id generic over
  path data: CId (IdOver: the type, tpI-ext, proj, Refl; DConj = the
  dependent-conjunction hypothesis, DCL.dc-at/dc-restr, dconj-cong; orS),
  CJ (J from a contraction: centre, natural line, cofibration; beta),
  CIdJ (the contraction of G.A.Id(a, q); J and beta), CIdFib (composition
  from the path composition + DConj; IdFib.fib), CIdCart + CIdNat (the
  composition commutes with moves), CIdEquiv (proj Id -> Path is an
  equivalence; IdEquiv.equiv), CIdEquivNat (its naturality, in move form:
  the equivalence over D is the move along the carts of CIdCart and
  CPathCart; IdEquivNat.nat); CSieve.DConjS (decidable sieves have
  dependent conjunction); instances CPosId, CDeltaId (constructive).
  model.tex §9.2 (strict J for Path on Delta, classical) is on paper only.

- L9 Localisation of the poset model (localisation.tex; 2026-10-17,
  seg-62; sits after the instances in All.seg):
  §1 the restriction i* to Delta: CLocRestr (R[G].iG, T[A].iA, rdG, rdA);
  §2 Lemma comp -> horn: CLocHorn (HornOfFib[G, A, c].horn : DH.isFib, the
  two cases of CBoxHorn's retraction: k = 0 from e0, k >= 1 from e1);
  §3 D, eta, mu and the strict monad laws: CLocD (port of model D.seg plus
  Laws.mu-assoc);
  §4 Theorem DA: a horn op on i*A gives a fibration of DA, from the
  face-uniform fillers CDFill.FT/FF through the Eilenberg-Zilber extension:
  CLocEZ (image factorisation of a Delta map h = m sigma with section,
  locked after Uq; EZP for a point (G, J) of the prism; EZK, two
  factorisations through k; HPr, the shuffle factor and pairs; VH,
  values of strict maps), CLocCompV (the value sigma^*(u_c(id)) of the side
  at a prism point; fibre constancy, Ind, naturality NatV, end condition
  EndC, VInj/StP at strict points, SV along strict maps), CLocCompP (the
  problem at f as a Delta problem PF.prob; RS: restricted along a strict
  map; PRe: invariant under restricting the poset data), CLocComp (CO: kop
  with Compat by FacesGen, kside on the side's sieve, kunif; Thm[G, A,
  hf].fib : Lines[G, DA].Fib; OfFib from a poset fibration of A).
  Naturality by the universal route: CLocDCart (D preserves cartesian
  maps: DK), CLocDUniv (DElFib on D El from CPosEl4.elFib; DF[D, c].fib
  for a code map c, moved along DK of CSmall.SmallFib.C; Nat: DF at c t is
  DF at c moved along DK of El(c t) -> El(c), by CCartLaws2 compFib +
  congFib, no filler moved).  The L9 files are at levels a (base) and l
  (presheaves), so Theorem DA applies to the universe (l = a+).
  §5 homotopies: CLocHtpy (HT for CLocD's maps over CHtpyOps.HT; DH =
  Lemma D-htpy), CLocPath + CLocPathEnd (quarry ports: the element of DDA
  over X * [1], its ends and naturality; Sum is L0, no CLocSum), CLocEtaH
  (Lemma eta-path as a homotopy eta_DA ~ D eta_A, no composition of A),
  CLocEq (Corollary: (i) mu . D eta = id and id ~ D eta . mu with no
  fibrancy; (ii) for fibrant A, D eta_A and eta_DA are homotopy
  equivalences, DDA fibrant by Theorem DA twice).
  Universal property of eta (prop:univ, [CRS] Thm 1.10 (2)=>(1)): CLocUniv
  (isModal B = HEq for eta_B; dModal from CLocEq (ii); etaU and Dcomp
  strict; for B fibrant and modal, G(u) = p_B . D u: G(u) . eta_A ~ u
  and G(f . eta_A) ~ f, composed in B by CHtpyOps.Inv/Cat).

Final statements: Theorem 7 (CThm7.Thm7, any base); ua as a ContrOp and
FibU.fibU for posets (CPosFinal) and simplicial sets (CDeltaFinal).

## Discipline

Every file < 5 s; lock a construction right after its characterising
lemmas; a slow file is a statement to fix.  All checks go through the
checking server: `./segc core changed` (gate), `check M`, `all`.
Report per layer: lines against the model layers it replaces, slowest files.
