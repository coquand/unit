# The cobar construction D on the cubical base (jonas.pdf §4)

Goal (DUALITY.md §6, item 2): check Lemma 11, Lemma 12, Lemma 14 and
Prop 13 for a concrete D, in sag-model's external (strict) style.

## Split

- canonicity-45: the presheaf layer PSh(C) over the base for C a V-small
  category, U, R, E = RU, and Lemmas 8 and 9 (representation choice in its
  design note).
- canonicity-4e: the weights P_n, D (Definition 10), Lemma 11, Lemma 12,
  then Lemma 14 and Prop 13.

## D in explicit form (the paper's notation after Definition 10)

For x : C0, an element of (DΓ)_x is a family

    u_{f0,...,fn}(i) : Γ_{x_n}

indexed by n ≥ 0, a chain of composable maps f0 : x0 -> x, ...,
fn : x_n -> x_{n-1} of C, and i : P_n, subject to (eq. (1)), for k < n:

    u_{f0,...,fk,f(k+1),...,fn}(∂_k i) = u_{f0,...,fk f(k+1),...,fn}(i)
    u_{f0,...,f(n-1),fn}(∂_n i)       = u_{f0,...,f(n-1)}(i) . fn

and (DA)_γ likewise, with u_{f..}(i) : A_{x_n}(γ_{f..}(i)). The unit is
τ(γ)_{f0..fn}(i) = γ . (f0 ... fn). This form never iterates E: D is
defined from C's chains directly, and E, R appear only in proofs.

## Weights

P_n ⊆ I^{n+1}: sequences with at least one coordinate equal to 1, i.e.
the union over k of [i_k = 1] (a cofibration of I^{n+1}: bigU of pre of
ptS e1 along the coordinates). ∂_k : P_{n-1} -> P_n inserts 0 at k.
Cosemisimplicial identities ∂_l ∂_k = ∂_k ∂_(l-1) for k < l.

## Lemma 12 in this form

Given a levelwise trivial fibrancy structure α on A (at every x : C0),
extend a partial element u of (DA)_x γ on φ by induction on the truncation
level m: at level m+1 and chain f0..f(m+1), the value u_{f..}(i) is fixed
on [i_k = 0] for each k (by (1), from level m) and on φ; glue these sides
(CPartial.Join over φ ∨ ⋁_k [i_k = 0]) and extend with α at x_(m+1). The
compatibility of the sides on overlaps is the cosemisimplicial identity.
Uniformity (commuting with restriction) holds because α does.

## Coding plan for D (canonicity-4e, 2026-11-10)

canonicity-45's layer (approved): option (b), C-indexed families of base
presheaves (CCtx: ob x : PCtx, act f : PSub), CTy likewise, LFib/LTriv
levelwise (pure reuse of Lines.Fib / ContrOp at each x), UTriv/CUnif
uniform in C via mapside; C at level a.

D_x from existing presheaf formers (Psh: Sigma, extensional Id, Pi), so
that naturality in the base direction is free:

    (DΓ)_x = Σ (u : Π_{n : N} Π_{ch : Ch_n(x)} Π_{i : P_n} Γ_{last ch})
               . (face equations (1) as Id types)

with N and Ch_n(x) (chains of length n+1 ending at x) constant presheaves
(V-codes: natV, SigV over C's obV/homV), and P_n a base presheaf: at stage
J, i : Fin(n+1) -> Hom J Iv with Lands J J (bigU J (n+1) (k |-> pre J Iv
(i k) (ptS e1))) (idH J); Lands is a proposition, so its proofs code by a
fixed code. Faces ∂_k: insert ptH J e0 at k; membership by bigU-in after
bigU-out.

## Representation of D (canonicity-45, Cobar.seg, in progress)

Chains have the last object as an index: Ch n x z (Chains.seg), with
comp n k (k <= n), drop n (top face, returns (z', c', last map)), rx
(C-action), and the semisimplicial identities. An element of (DΓ)_x at
base stage X is t with t n z c J g i : (Γ.ob z).ob J for c : Ch n x z,
g : J -> X, i : Pn n J; natural in J; inner faces
t (n+1) z c J g (d_k i) = t n z (comp n k c) J g i; top face
t (n+1) z c J g (d_(n+1) i) = Γ.act fm (t n z' c' J g i).

## Lemma 12 (trivial fibrancy), detailed proof for the formalisation

Input: α z : ContrOp (Γ.ob z) (A.ty z) for every z (levelwise; LTriv).
Output: UTriv (DΓ) (DA).

Fix x, a base stage X, γ in (DΓ)_x(X) and a side s of DA over γ: a
cofibration Q on X and partial values s_h for h : W -> X landing in Q
(each an element of (DA)_x(W, γ.h), natural in W). We build
u : (DA)_x(X, γ), i.e. u n z c J g i in A_z(J, γ n z c J g i), level by
level.

Level n, at (z, c, J, g, i). Solve one extension problem for α z at
stage J over γ n z c J g i, with cofibration

    Q_{n,g,i} = pre g Q  ∨  ⋁_{k <= n} [i_k = 0]      (a bigU on J)

and partial element given by
  - on pre g Q (h : W -> J landing): (s_{g h}) n z c W (id) (res h i);
  - on [i_k = 0] (h landing, so i.h = d_k i' for a unique i' : Pn (n-1) W):
      for k < n: u (n-1) z (comp (n-1) k c) W (g h) i'   (level n-1),
      for k = n: A.act fm (u (n-1) z' c' W (g h) i')     (drop).
Set u n z c J g i := (α z).kop J (γ n z c J g i) (that side).

Compatibility of the pieces (needed for Join):
  - [i_k = 0] ∧ [i_l = 0], k < l: by the faces of u at level n-1 and the
    semisimplicial identities (comp-comp, comp-drop, drop-drop) and the
    weight identity d_l d_k = d_k d_(l-1);
  - pre g Q ∧ [i_k = 0]: s is itself an element of DA, so it satisfies
    the faces.
Naturality in J: α's uniformity (kunif) and the naturality of the side's
pieces. Faces at level n: at a weight d_k i' the face [i_k = 0] is total,
so the extension equals the side there (rc-ext / the extension law of
ContrOp). Extension of s: on pre Q the side is s, hence u extends s.
Uniformity in C (CUnif): the construction at (x', rx g c) is literally
the one at (x, c) (u is defined by recursion on n, uniformly in c), so
the C-action commutes strictly, as in Lemma 9.

Formal shape: a record Up m of the levels n <= m with naturality, faces
and extension of s; step : Up m -> Up (m+1) extending; u n := the level n
of the m-th stage for m >= n (levels are never changed once built).

## Status

- Lemma 12 CHECKED (canonicity-45, Lemma12.seg): `L12[C,G,A].lemma12U al : UTriv (D G) (D A)`,
  with `lemma12 al x : ContrOp ((D G)_x) ((D A)_x)` levelwise. Premises: only `al` (a levelwise
  ContrOp of A) and the base's CB fields (through PosFull.PB); no new axioms. The uniformity in C is
  not strict here: it is a second induction on levels (KC), like kunif (KU), using K.rx-fc.
  Negative tests: dropping W3 in FFS, or rx-fc in KC, fails.

## Plan: Lemma 14 (U τ_A is an equivalence), at a component x

Input: fibrancy of DA at x (Lemma12F.fibD, levelwise suffices).
- ε : (DA)_x γ -> A_x γ, u |-> u at (n = 0, chain id_x : Ch 0 x x, weight (1)).
  ε τ = id strictly (τ at the identity chain and weight (1)).
- τ ε ~ id: two lines in (DA)_x over the constant line at γ, i.e.
    q_{f0..fn}(i) at j = u_{id,f0..fn}(j, i)            (j=0: face d_0, = u_{f..}(i); j=1: (1, i))
    p_{f0..fn}(i) at j = u_{id,f0..fn}(1, j ∧ i)        (j=0: (1,0,..,0) = top faces, = u_id(1) f0..fn;
                                                         j=1: (1, i))
  Each is an element of DA over stage X × I, so its D-equations are checked
  pointwise (faces of (j, i), (1, j ∧ i) by Weights + K.fc).
  Then compose p · q⁻¹ with fibD at x.
- New weights operations (Weights.seg, canonicity-4e): cons j i : P_(n+1)
  (prepend a coordinate, in P when j = 1 or i in P), cons-face (d_0 (cons 0 i)
  = ...), meet j i (coordinatewise min with the connection cI true), and the
  face laws of cons / meet. Chains: prepend id (K.consId) with its faces.
- Output: U τ_A is bi-invertible at x (strict retraction ε, homotopy section
  p · q⁻¹), stated with the base's path types.

## Plan: Prop 13 (Df is an equivalence when U f is)

Input: f : A -> B over Γ (C-types), Fib of A and B levelwise, U f an
equivalence levelwise.
- P := homotopy fibre of f, a C-type over Γ.B (Σ over A, path type in B):
  needs Σ and path types of C-types (CPshL has lines; Σ pointwise).
- Levelwise: U f an equivalence of fibrant types => U P trivially fibrant
  (base fact: equivalences have contractible fibres, then ContrOp;
  sag-model FibContr / FibHt / S3).
- lemma12U on P: UTriv (D(Γ.B)) (D P).
- Lemma 11 for homotopy fibres: Psi from the homotopy fibre of D f to D P,
  in CMove.Mv's shape, following Lemma11L's PsiL / PsiPt / PS / BK patterns.
- Hence the homotopy fibres of D f are trivially fibrant, so D f is an
  equivalence (at each x: ContrOp of fibres => contractible fibres =>
  equivalence, FibContr; is-equiv is a proposition, so compatibility in C
  is automatic).

Lemma 14 (canonicity-45, Lemma14.seg, f81f7f93): `L14.lemma14 al x : QInv x`
for A levelwise fibrant: over G_x, with B = D A pulled back along tau,
eps_A (u at (0, x, id, X, id, (1))), eps tau ~ id (Ret on Rf) and
tau eps ~ id = Cat p (Inv q), where q : id ~ m and p : tau eps ~ m are MW
lines (u at (n+1, consId c, W i) for the weights ConsP (j g) i and
consOne (meetC (j g) i)); the composition of B is lemma12F's fibD along tau.
p's j = 0 end is P0.R, by induction on n through u's top equations
(TopOne) and tE-o / tot-drop.  No new axioms beyond the named premises.

Prop 13 (canonicity-45, Prop13.seg, a0dc0734): `P13Of.Main.prop13 x :
EquivOp (D f at x)` for f : A -> B a CMap with ef : EquivOp (U f) levelwise
(fA, fB taken as in the paper, unused by the proof).  The homotopy fibre P
of f is a C-type over G.B (HP.PC); lemma12U on (G.B, P) with LTriv = ef;
Psi from the fibres of D f to D P (PSI: sP, mS, mSnat, mTinj, BK.bk,
BK.bkMv) moves it by CMove.Mv.  Levelwise in x; the uniform form (D f an
equivalence in PSh(C)) is not done.  EquivOp is the base equivalence
(sag-model S3 relates it to is-equiv).  No new axioms beyond the named
premises.

Corollary 15 (canonicity-45, Cor15.seg + QinvEq.seg): `C15[C,G,A].Main[al].cor15 x :
EquivOp (D tau_A at x)` for A levelwise fibrant (al), where tau_A : A -> DAC is a CMap
(DAC = D A over G, DCTy pulled back along tau by subCTy; naturality in C by tot-rx and
A.tE-o) and DAC is levelwise fibrant by Lemma 12 along tau (CFibSub).  It is Prop 13 at
f = tau_A with ef from Lemma 14.  QinvEq.seg is the base-level bridge needed for ef:
`QE[G,A,B,f,g,eta,eps].qinvEq : EquivOp f` from a core quasi-inverse (NMaps f, g and
HT homotopies g f ~ id, f g ~ id) between fibrant types, through the CwF of fibrant
types: FunOf (an NMap as lam of its reading), AppW (the value of app (wkF w) a at a
point, by CwFOv.bodNat and FibIdRd.elTr), HtpyOf (a homotopy as an element of EQ.Htpy
by FibNF.LineY), CwFS4.kOf (Escardo), FibS3 S3b, and CHFibCart.moveEq (bod (lam fP) = f
by app-lam).  Negative tests: dropping A.tE-o in tauA's naturality, or the app-lam
retargeting, fails.  No new axioms beyond the named premises.

## Plan: Lemma 54 (U preserves Π with domain in κ), concrete form

Lemma 54 has content only for the general Π of PSh(C) (internal to cSet),
which the C-layer does not have yet. Plan:
1. Π for C-types (CPi.seg): for A : CTy[G], B : CTy[ExtC G A],
   (Π_A B)_x at stage X over γ = families b over (y, f : y -> x, Y, h : Y -> X,
   a in A_y(Y, act f (γ h))) with values in B_y(Y, (act f (γ h), a)),
   natural in (f, h) (an end over C/x and the base); coded like CPshR's
   Prod plus CLine.FC's naturality. C-action: precompose f. Then lam / app
   with β, η, and stability under C-substitution (the CwF laws of Π).
2. Constant domain: ΔK for an external finite set K (V-coded Fin n), the
   C-type with A_y = K at every stage and identity actions.
3. Lemma 54: (Π_{ΔK} B)_x ≅ Π_{k : K} B_x(k), by restriction to f = id_x,
   h = id_X; the inverse uses naturality (a family over (f, h, k) is
   determined by its values at the identities, since ΔK's action is the
   identity). Stated as a fibrewise bijection (as lemma11-lines), natural
   in x.
Owner: canonicity-45 after Lemma 16 (Π for C-types is CPshR-style coding);
canonicity-4e reviews.

Prop 13, INTERNAL form (canonicity-45, Prop13U.seg): `P13U[C,G,A,B,f,fA,fB,ef].prop13U :
Unif[HPD.GB, HPD.PC, HPD.PC, id, prop13].CUnif`, the C-uniformity of the fibre contractions
(the paper's element of is-equiv(D f) in PSh(C); "is-equiv is a proposition" gives
C-compatibility only up to a path, so this is needed, 4e's ruling 2026-11-11).  DfC = D f as
a CMap over D G (naturality by DM.pc both ways), HPD = its homotopy fibres as a C-type,
PU.sPC / PU.mSC = Psi commutes with the C-action (refl on points; HPD.rb for the A part),
PU2.res = the Lemma12F.UFl argument (mTinj, kopMv, lemma12U's CUnif, kop-cong along the
side equality R).  Negative test: dropping lemma12U's uniformity step fails.
Corollary 15, internal form: `C15.Main.cor15U` = prop13U at f = tau_A (Cor15.seg).

## Lemma 16: why the zig-zag (2026-11-11)

Lemma 14's inverse eps (read at the identity chain and weight (1)) is NOT natural in
C: eps(u.g) = u_g(1) while eps(u).g = u_id(1).g, the two corners (0,1) and (1,0) of
u_(id,g), equal only up to the line t |-> u_(id,g)(1,t) . t |-> u_(id,g)(t,1).  So U tau_A
has a levelwise inverse but tau_A has no inverse in PSh(C); Lemma 16 (tau_DA an
equivalence in PSh(C)) needs the zig-zag D tau_A ~ tau_DA with D tau_A a genuine
morphism (Cor 15) and the internal invariance of is-equiv under homotopy.
Ruling (4e, 2026-11-11): (C) build the C-natural zig-zag K and the levelwise Lemma 16
(Lemma 14 at DAC + QinvEq); the uniform Lemma 16 is recorded as conditional on the
named statement "uniform EquivOp is invariant under a C-natural homotopy" (the
internal invariance of is-equiv in PSh(C)Fib), to be discharged by (B): PSh(C)Fib as
a CwF instance (C-level Sigma, Pi, Id with uniform fibrancy + an S3-style bridge),
which also gives Lemma 54 its Pi.  (A) (hand-made path algebra on fibres) is ruled out.

Lemma 16 (canonicity-45, Lemma16.seg): the zig-zag homotopy and the levelwise statement.
`L16[C,G,A].Main[al].zig x : HT[G_x, DAC_x, B2_x, dTau x, tauD x]` with B2 x = (D DAC)[tau_G]
at x, dTau = D tau_A pulled back along tau_G (a natural map DAC_x -> B2_x by DF.DN's
argument at the points tau gm), tauD = Lemma 14's tauN at DAC.  zig = Cat q (Inv p),
composed with Lemma 12 at DAC along tau (fB2), where p : tauD ~ M and q : dTau ~ M are
the paper's lines (meets with t on the left, resp. right block of a concatenated weight)
and M u is the bridge u_(cat c' c)(cat j' i).  Machinery: MW2 = the double reading of u at
(cat c' c, Wf (j'|g') i) for a weight family Wf with laws Wres / WfaceL / WfaceR (right
faces with the transport along plus-suc, Weights.catFR by 4e), as an element of B2_x:
inner equations by comp-back / drop-cat, outer by cat-left / cat-junction (the C-action
of DA); MWN2 (base naturality), LN2 / LP2 (lines -> homotopy), MWEq2; the ends by the
front induction (Front: m+1 faces at 0, cat-front) and the back induction (BK.Back: n+1
top faces, drop-cat / drop-cat0, catZeroTop, zerosTop); the three families WfCat, WfML,
WfMR with their laws from catC-res / catFL / catFR / MeetFace.
`Main[al].lemma16 x : EquivOp (tauD x)` = Lemma 14 at DAC + QinvEq (levelwise Lemma 16).
Negative tests: the wrong end (meet at 1) in p's start, or dropping cat-junction in the
outer top face, fail.  No new axioms beyond the named premises (al, CB).
NOT done (ruling (C)): the C-naturality of zig and the uniform EquivOp of tauD, which
need "uniform EquivOp is invariant under a C-natural homotopy" = (B).
C-naturality (ruling (C), 2026-11-11): the lines p, q ARE natural in C: `L16.LC[x',x,gC,X,z,V,f,j].pC / qC`
(the value of the line at z moved along gC is the value at the moved point; MWC = the moved double
reading is the double reading of the moved element, by rx-cat and the reading of a coerced D-element).
NOT done: the C-naturality of zig = Cat q (Inv p) itself, which needs "CHtpyOps.Cat / Inv commute with a
C-action when the homotopies do and the composition is C-uniform" (CPathComp's composite, a Lemma12F.UFl-
sized generic lemma); under (B) the composition is the C-level fibrancy's.  Recorded as: zig is C-natural
modulo the uniformity of Cat / Inv.

## (B) PSh(C)Fib as a CwF instance (canonicity-45, from 2026-11-11; approved by 4e)

Stage 1(i) DONE: `CPCwF.seg: CwFOf[C].CPCwF : CwF.CwF[l+]`, the raw CwF of C-presheaves
(Ctx = CCtx, Sub = CSub, Ty = CTy, El = CEl, ext = ExtC, p = pPC, subT = subCTy, with cidC,
coC, nilC, epsC, subCEl, qC, liftC, secC).  `CPshExt.seg`: record extensionality and set-ness
for CSub / CEl / CTy (csub-ext, cel-ext, cty-ext2 with the actions compared along the paths of
types; isSet-CSub / isSet-CEl / isSet-CTy; tyTr-same: transport of a total along a path of
types with equal object parts is the fibre transport, TOb a set).  Every CwF law is the base's
law at each x: the transport of a C-element / C-substitution along a path of C-types is the
transport along the base path at each x (elTrC, sbTrC, PTy a set), so subEl-id / subEl-o /
liftP-id / liftP-o / qP-liftP / qP-secP are the components of the corresponding laws; subT-id /
subT-o by cty-ext2 with the readings rB (SC.rBtE).  Negative test: dropping rBtE in subT-id's
action comparison fails.

Stage 1(ii) DONE: `CPshUFib.seg: UFibOf[C].CFibCwF : CwF.CwF[l+]`, the CwF of fibrant C-types =
CwFCl.ClCwF at Cl := UFib (CPshL.UF: levelwise compositions commuting with the C-action).
clSubU (UFib along a CSub) = CFibSub.FibSub at each x, with the uniformity of the moved family
proved in the Lemma12F.UFl pattern through the cartesian map of the substitution (UP: sVC / mSC /
mTC = the point map, the strict-fibre map and the map of totals of the other end commute with the
C-actions, by sb-nat and SC.rBtE; msideC; then mTinj, kopMv, A's uniformity, kop-cong).  isSet-UFib
(LFib a set, the uniformity halves propositions); clSubU-id / clSubU-o = the base's FibClL laws at
each x (fibTrC: the transport of a uniform fibration along a path of C-types is the base transport
at each x, PTy a set; sigSnd).  Negative test: dropping A's uniformity step in UP.Res fails.

Stage 2(c), Pi (canonicity-c2, from 2026-11-10).
`CPshPi.seg: PiOf[C].PiC[G, A, B].PiT : CTy[G]`, the C-type Pi_A B = eta^* R of the base
products (PresheafPi) of (A_y, B_y), cut by naturality in C.  Fibre `At[x, X, gm].PiIx` =
(b : Comp) * CNat b, with b y f in the base product at act f gm; code piO = SigV (CPshR.Prod ..)
(propV (CNat b)), propV the truth value of a proposition (propV-ext by extensionality of V).
Base action Act (componentwise), C-action CAct (reindexing b y (g f)).  Method: one normal form,
`valAt b y f Y h w` = the value of b y f at stage h and at a TOTAL w of A_y (valAt-cong: it
depends on f, h, w only), `tot-ext` (totals of Pi are equal when their points and values are),
and the value lemmas valAct-at (h becomes k h), valRix-at (f becomes g f), cnat-at (B.tE g: f
becomes f g, w becomes A.tE g w).  Negative test: dropping co-idl in tE-id fails.
`CPshPiLaws.seg: PiLawOf[C].L[G, A, B]`: the restriction to identities `resT x X wP w` (the value
of a total wP of Pi at f = id_x, h = id_X and w; shared with the Sigma / Id bridge), res-C,
res-B (it commutes with the C-actions and the base actions), val-res (every value is a
restriction of the moved total), valNat-at (base naturality of values); `App[t].app`,
`Lam[v].lam`, beta, eta, `PiIso : Iso (CEl[G, PiT]) (CEl[G.A, B])`.  Negative test: dropping the
unit-law step in res-C fails.  Writing note: VR.res as one nested term made the checker spin;
with named steps it takes 0.3 s (WRITING.md rule 4).
`Lemma54.seg: L54Of[C].M[G, A, B, ca].lemma54 x X gm`: for A cartesian (`Cart[G, A]`: the
C-action of A is a bijection on fibres), the fibre of Pi_A B at x is in bijection with the fibre
of the base product of A_x, B_x (cmpE = the component at id_x, natural in the base by cmp-B;
inverse phi |-> B.tE f . phi . back).  Instances: constCtx / constTy / cartConst (a base type
with identity C-actions), CartSub (stability under C-substitution), `Delta[G0, K, G, s].lemma54K`
(the paper's Lemma 54, Delta K over any C-context).  Negative test: dropping cnat-at in inv-cmp
fails.  Premises: fe (and univ only through V's extensionality in propV-ext, not yet used).
`CPshPiNat.seg: NatOf[C].N[D, G, s, A, B].PiT-nat : Id (CTy[D]) (subCTy D G s (Pi_A B))
(Pi_{A[s]} B[lift s])`.  tr b y f = b y f moved along s.sb-nat, then along the base Pi-nat at y
(a path of types, tyTr); TV.res: the values of tr b, read in G, are the values of b; natTo /
natFrom: b is natural in C iff tr b is; codes equal by SigV-cong and propV-ext; Pf x by ty-ext2
(PW: the base actions agree componentwise); QQ: the C-actions agree (transports of one component
along paths of points).  Negative test: cnat-at replaced by refl in natTo fails.
`CPshPiStr.seg: StrOf[C].PiC : CwF.Formers[l+, CPCwF].PiStr`, the Pi structure on the raw CwF of
C-presheaves (Pi, Pi-nat, Pi-iso = PiIso, Pi-iso-nat = IN.res: apd-el + the base's Pi-iso-nat at
each y).  Negative test: dropping the base Pi-iso-nat fails.
Premises: fe; univ only through V.seg's extensionality of iterative sets (propV-ext).
Uniform fibrancy of Pi, in progress (canonicity-c2).
M1 DONE, `CPshPiFib.seg: FibOf[C].Fr[G, A, B, x, e, e'].Cp[cT].Wn[nc].comp`: the composition of
(Pi_A B)_x from compositions cT y f of the components T y f = (base Pi at y)[act f] over G_x and
the hypothesis NatComp (module parameter nc; the component composites are natural in C).
al y f = the projection (a PMap over G_x), CMapLine moves points / lines / sides, kside / kunif
componentwise (tot-extC, endM-rd).
M2, NatComp DONE, `CPshPiFibN.seg: NOf[C].Nd[G, A, B, x, d, kA, cB].NC[kAU, cBU].natComp : Cq.NatComp`
and `.comp`, the composition of (Pi_A B)_x from src d to tgt d, with cT y f := CFibSub's
MoveComp.move of CPi.PiC[G_y, A_y, B_y, d, kA y, cB y].comp, kAU = the fillers kA are C-uniform at
the end tgt d, cBU = UComp of cB.  Steps: Val.compE (the component (y, f) of the composite is the
base composite CopX.cop at the moved data: kopMv, sVE); Val.VK.res (its value at (h, a0) is
rdB (wB, bB) of CPi.Prob at the restricted data); At2.LaC (the reverse A-line moves along g: kAU at
the empty side); At2.ptB (the point of the B-problem moves: LaC, and CPshPiAp.apC at the start,
which is the projection of the start of the line of (Pi_A B)_x, Q0); At2.SdV / sdB (its side
moves: pv-pt, pv-lev, apC on the values of ApL, the line of the side being the projection of the
line of p, QLy / QLz); At2.Core (CPshFillU's rdC for B, cBU, kop-cong).  `CPshPiAp.seg`: the
bridge apW-valAt between CPiE.apW and valAt, and apC (naturality in C of application).
Negative test: apC replaced by refl in SdV fails.
M2, UComp DONE, `CPshPiFibU.seg: UOf[C].Ud[G, A, B, d, kA, cB, kAU, cBU].ucomp :
LO.UF[G, PiT].UComp (src d) (tgt d) comp`: the component (y, f') of the composite at x, moved along
g : x' -> x, is its component (y, g f') (prC, G.act-o); both it and the component (y, f') of the
composite at x' are the base composite of Pi_y (compE) at data which agree (eWg for the points,
tsEg for the sides), so kop-cong applies.  RdG: the reading lemma for an abstract C-type (stated
directly at PiT it overran the 10 s limit).  Negative test: dropping prC in Wy.q1 fails.
M3a DONE, `CPshPiFibF.seg: PFOf[C].PF[G, A, B, uA, uB].piUFib : LO.UF[G, PiT].UFib`: Pi of uniformly
fibrant C-types is uniformly fibrant (each direction d: kA := CFill.FillC of A's composition in the
other direction, kAU := CPshFillU.FU.res, cB / cBU from uB; then CPshPiFibN.comp, CPshPiFibU.ucomp).
M3b DONE: Pi on the CwF of uniformly fibrant C-types.
`CPshPiFibS.seg: SOf[C].Sx[D, G, s, A, B, x]`: K, the cartesian map from (Pi_{A[s]} B[lift s])_x to
(Pi_A B)_x over s_x (transport back along CPshPiNat's Pf x, then the lift, as CPiCart); MN =
FibCwF.MoveNat for it; `Py.prS`: the (y, f) projection of a total read by K, read in Pi_y, is
CPiCart's reading at y of the (y, f) projection (trFst, trV-tyTr / tyTr-trV); `Hd[d, kA, cB, kA', cB',
cmpY].Hn[ncG, ncD].uniq`: the composition of the substituted product at x is the move along K of
that of the product (MoveComp.unique; componentwise, read in Pi_y: prS, Val.compE on both sides,
CPiCart's kopMv with cmpY, and the moved data agree, eWs / tsEs, kop-cong).  Negative test:
dropping prS fails.
`CPshPiFibC.seg: PiClOf[C]`: piCl := piUFib; `PNat[D, G, A, B, s].Bx[x].base`, the levelwise law
(MN.law, then uniq in the two directions with cmpY := the two halves of the base's
CPiNat.PiNat[...].nat at each y; its inputs are clSubU's structures on the nose, no bridging
equality was needed); `PNat.law` = piCl-nat in the shape of CPshSigFib.SNat.law;
`FPiC = UF.FCC.ClPi[CPshPiStr.PiC, piCl, piCl-nat]`, so `FPiC.SPi` is the Pi structure of CFibCwF.
NF, raw form DONE, `CPshNF.seg: NFOf[C].NFC[G, A, B, f, g, h].nf : CEl[G, IdC[G, PiT, f, g].IdT]`, for
f g : CEl[G, PiT] and h : CEl[G.A, IdC[G.A, B, app f, app g].IdT] (canonicity-45's CPshId).
(A) `LineYC`: a line field Lf x W y j of a C-type, natural in the base (Unat) and in C (UC), with
ends a0, b0, is an element of Id(a0, b0): the base's FibNF.LineY at each x, C-natural by
CPshId.rd-C / idC-eq (empty sieves).  (B) `Hx[x].hv` / `hvT`: the value of the path h z at
(K, id, j), natural in the base (hvT-nat) and in C (hvT-C: rd-C and h.el-nat), with ends app f,
app g (hvT-0, hvT-1); `LfAt`: the line field of Pi, component (y', f') built by Lemma54's
KB.AtK.mk from the values hv y' K (.., a1) (j m); UN, UE (ends: CPshPiLaws.Eta's e1-e3), UC.
Negative test: hvT-C replaced by refl in lfN fails.  Lemma54: AtK moved to the module KB (no
Cart hypothesis) so that NF can use its constructor mk.
Not done: NF on CFibCwF (the instance at the fibrant Pi and Id), which waits for the Id closure
and J on CFibCwF (CPshIdJ, canonicity-45).

### (B) stage 2(a): Sigma (canonicity-45, 2026-11-10)

`CPshSig.seg`: `SigOf[C].PSigC : CwF.Formers[l+, CPCwF].SigStr`, the Sigma
types of C-presheaves on the raw CwF.  `SG[G, A, B].SigC` is the base's
`SigAB` at each x with the C-action `unflat . B.tE . flat` (a Sigma-total
flattened to a total of B), so the laws are B's; `SigNatC[D, G, s, A, B]`
gives Sig-nat (cty-ext2 with the base's SigNat at each x) and Sig-iso-nat
(the base's iso-nat at each x, transported with `elTrC` + `isSet-PTy`).
Checker observation (ten-second rule): Sig-iso-nat's statement mentions
the record's `coerce`, whose type is `subT D (ext D (subT D G A s))
(subT (ext ..) (ext G A) B (lift ..)) (sec ..)`; converting that against
the same type in the LOf spelling, nested inside the outer subT, takes
more than 10 s, although each argument converts alone in under a second
and the deep term compared with itself is instant.  Remedy: SigNatC
instantiates `SG` at D with the record's own spelling of A[s] and
B[lift s], so the SigStr's field types meet the instance syntactically;
the file checks in 4 s.  Minimal input kept in canonicity-45's scratchpad
(slow-conversion-probe.txt).  Negative test: dropping the B.tE-pt step of
SigC's tE-pt fails.

`CPshFillU.seg` (the shared lemma for Sigma, Id and Pi): `FillUOf[C].FU[G, A,
d, kk, cu].res` — the derived fillers `CFill.FillC[G.ob x, A.ty x, d, kk
x].fill` of a C-uniform family of compositions kk (cu : LO.UF[G, A].UComp
(src d) (tgt d) kk) are C-uniform, as `P.Unif[SF.TVC, SF.SFC, SF.SFC,
pmap-id, fill].CUnif`; pointwise form `fill-C`.  Mirror of CFillMove for
the C-action (not cartesian): the problem at a point moves (PMC: pt,
sd-eq, out through cu and kop-cong), restriction commutes with the
C-action of sides (inpEq).  Negative test: replacing the inpEq step of
fill-C by refl fails.  Next: sigCl (CSig.SigFib at each x + the
C-uniformity of its composite, mirroring CSigNat with FU), then Id.

`CPshSigFib.seg`: `SigFibOf[C].sigCl G A B : UF.Cl G (SG.SigC)` — Sigma of
uniformly fibrant C-types is uniformly fibrant: CSig.SigFib at each x,
and `SU[G, A, B, d, kA, cuA, kB, cuB].res` (the Sigma composite is
C-uniform; mirror of CSigNat.SigNatC.H for the C-action: the A fillers by
CPshFillU.FU.fill-C, the B composites by cuB, the readings of the Sigma
composites by tt-ext).  `SNat.law` is CwFCl.ClSig's law, the base's
FibCwF.SigN.law at each x (fibTrC + isSet-PTy + sigSnd, as clSubU-id);
`FSigC = UF.FCC.ClSig[PSigC, sigCl, law]`, so `FSigC.SSig` is the SigStr of
the CwF of fibrant C-types CFibCwF.  Negative test: replacing the
composite-agreement step kE-eq of H.res by refl fails.  Stage 2(a) done.

### (B) stage 2(b): Id (canonicity-45, 2026-11-10)

`CPshId.seg`: `IdOf[C].IdC[G, A, a, b].IdT : CTy[G]`, Swan's identity type
in Yoneda form (PosIdY.IdY) as a C-type, with `IdT.ty x = IdY[G.ob x, A.ty
x, a.el x, b.el x].IdYT` on the nose.  The C-action along f : y -> x sends an
element at (X, g) to the element at (X, g f) whose readings are A.tE of its
readings (module TC: uY by fromE along A.tE-pt and G.act's naturality;
natY, mv as PosIdY.Tact) and whose sieve is its sieve; `rd-C`, `sieve-C`
and `idC-eq` (= tpY-ext: point, readings and sieve determine an element)
describe it completely; the laws tE-id, tE-o are idC-eq with A.tE-id,
A.tE-o on readings.  `IdNatC[D, G, s, A, a, b].nat` : Id(a , b)[s] =
Id(a[s] , b[s]) as C-types (the Id at D instantiated at the record's
spelling of A[s], a[s], b[s]): the base's IdYNat.nat at each x, the
actions compared on readings (IdYNat.tr-rd through CSub.SubE.mV-inj) and
sieves (tr-sq).  `ReflC[G, A, a].reflC : CEl[G, IdT]`: FibIdRd.ReflY at each
x, C-natural by readings and a.el-nat.  Negative test: dropping the point
transport (pi) in reflC's naturality fails.  Next: the UFib closure (the
Id compositions are C-uniform: path layer, core-Id layer, Yoneda iso, as
in the design note), then J with JNatT (generic, for any commuting map of
J-data and any uniform family of compositions).
