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

The S3 bridge at the C-level (canonicity-c2, from 2026-11-11; route approved by 4e): port FibS3's
three ingredients instead of reading the internal element through nested formers.  (I) raw
internal contractibility (a centre c : CEl[G, T] and a contraction ctr : CEl[G.T, Id(c[p], q)]) <=>
UTriv G T; (II) the fibres FV / HFib and the generic transfer U-Rel; (III) packaging on CFibCwF
after CPshIdJ.  Final statements S3a_C / S3b_C: internal equivalence on CFibCwF <=> EquivOp at
each x + CUnif of the fibre ContrOps (Prop13U's shape).
(I) C1 DONE, `CPshContr.seg: CtrOf[C].C1[G, T, ut].c / .ctr` (UTriv => centre and contraction): c at
x = the extension of the empty side, natural in C by uniformity (emp); ctr = the Connect line
field (FibContr.CO at each x), natural in C by uniformity and a side-ext on the Connect side
(UCm: vE, sdE, valC), then CPshNF.LineYC.  Negative test: dropping cnat in vE fails.
(II) U-Rel DONE, `CPshURel.seg: URelOf[C].URel[D, S, T, f, g, mId, fC, gC, ut].utS : UTriv D S`: for
maps f x : S_x -> T_x, g x : T_x -> S_x of base types (CHtpyOps.NMap) with g after f the identity
and both commuting with the C-actions, a uniform ContrOp of T gives one of S
(CLocBoundRetr.Relative + FibYC.RelId at each x; sdF: the moved f-image of a side is the f-image of
the moved side).  Negative test: dropping fC in sdF fails.
(II-a) base part DONE, `CPshFibMaps.seg: RawFib[G, Y, X, al]` (base level): FibS3's ends, YC, FV1,
HFibId and the four maps toS / frS / embS / prjS RESTATED ONCE on raw data (al a CPartial.PMap, no
packaged element of a function type; FibS3 itself goes through CwFFv.E); new: fN / gN / mId, core's
homotopy fibre HFib is a retract of FV1 = Sigma Y Id.
(II-a) C-level DONE, `CPshFibC.seg: FibCOf[C].Fb[G, Y, X, f]` (f : Prop13's CMap[G, Y, X]): the ends
a0C = f y (natural in C by f.mp-nat) and b0C = x as C-elements over Kc = G.X.Y; IdK = CPshId's IdC
on them; IdR = the same C-type with its type at x written in RawFib's names; `FVc` = CPshSig's SigC
over it, FVc.ty x = RawFib's FV1 on the nose; TF (the action on a total, rdR: its readings);
GC / FC: gN and fN commute with the C-actions (on readings, prX-C); `utHP : UTriv Dc FVc ->
UTriv Dc HP.PC` by U-Rel (HP = Prop13's homotopy fibre C-type).  Negative test: dropping prX-C in
FC fails.  Cost note (third checker observation): with the fibre written partly through
SigC / IdC's own names and partly through RawFib's, four small declarations took 6-10 s or overran;
written in one vocabulary the file takes 7 s, of which 4 s is the one rewrapping IdR.
(I) C2 DONE, `CPshContr.seg: CtrOf[C].C2[G, T, c, ctr].ut : UTriv G T.1` (T uniformly fibrant, c a
centre, ctr a contraction): at x, the extension by c relative to the constant map, corrected by T's
composition along the homotopy read from ctr (FibHt.YH, CLocBoundRetr.Correct); uniform in C by tC
(the homotopy's values move: CPshId.rd-C, ctr natural in C), wpC / sdC (the problem of Correct
moves), T's UComp e0 e1 and CPshPiFibU's RdG.rdC.  Negative test: dropping tC fails.
So, at the raw level, S3b_C holds: a centre and a contraction of FVc over G.X give (C2) UTriv of
FVc, hence (utHP) UTriv of Prop13's HP, i.e. EquivOp at each x + CUnif.
(II-b) base lemma DONE (ruling of 4e: Option C), `CPshIdExt.seg: IdExt[G, Y, X, al, eop].contrI /
.contrFV` (base level): a ContrOp of core's homotopy fibre Sigma Y Path gives one of
HFibId = Sigma Y IdOver, hence of FV1 = Sigma Y YonedaId (a retract of HFibId).  NEW ARGUMENT, not
the base's: FibS3's S3a goes through the equivalence Id -> Path (CIdEquiv, with the fillers of the
path type) and FibC2; here the extension of a side s is (y*, (p*, ph)) with (y*, p*) eop's
extension of the image of s and ph the dependent conjunction (CId.DCL, the construction CIdEquiv
uses for its ph) of s's sieve with the sieves of the Id parts of s; p* is constant on ph (Cc);
kside by DCL.dc-at, kunif by DCL.dc-restr.  So the base's S3a does not need the path fillers.
Negative test: the sieve equation dc-at replaced by refl fails.
(II-b) C-level DONE, `CPshFibC.seg: Fb[G, Y, X, f].SA[ut].utFV : UTriv Dc FVc` from
ut : UTriv Dc HP.PC: at each x CPshIdExt's contrFV; uniform in C by sdP (the image in HP of the
moved side is the moved image: GC), eHP (HP's uniformity), then the extension in FVc has the same
point (Pt), readings (Qr) and sieve (Qs: the C-action keeps sieves, CId.dconj-cong).  Negative
test: dropping eHP in Qr fails.
So at the RAW level both directions of the bridge are checked, for f : CMap[G, Y, X]:
  S3b: a centre and a contraction of FVc over G.X (FVc uniformly fibrant) => UTriv FVc (C2)
       => UTriv HP.PC (utHP), i.e. EquivOp at each x + CUnif (Prop13U's shape);
  S3a: UTriv HP.PC => UTriv FVc (SA.utFV) => a centre and a contraction of FVc (C1).
Not done: (III) packaging on CFibCwF (El of isContr / Kr on CFibCwF <=> centre + contraction, the
map as an element of the function type <=> CMap), which waits for canonicity-45's PIdJ; then the
invariance statement for Lemma 16.

## The S3 bridge on CFibCwF, packaged (canonicity-c2, 2026-11-11)

Checked, no new axioms.  CF = CFibCwF with FPiC.SPi, FSigC.SSig, PIdJ, NFCOf.nf.
  CPshContrC.ContrCOf[C]   toUT : El G (isContr G T) -> UTriv G T.1 ;  fromUT : the converse
  CPshFvC.FvCOf[C].Fv[G, X, Y, r]   al : CMap[G, Y.1, X.1] (the map of r : El G (Fun G Y X), by bod r);
                           e1v / e1eq: the end of the interface's fibre FVr is CPshFibC's a0C (celTr)
  CPshFvC2.FvC2Of[C].Fv[G, X, Y, r].fvEq : (QP.FVr G X Y r).1 = CPshFibC.Fb[G, Y.1, X.1, al].FVc
  CPshS3C.S3COf[C].S3[G, X, Y, r]
     S3b : El G (Kr G X Y r) -> UTriv (G.X) HP[G, Y.1, X.1, al].PC     (EquivOp at each x + CUnif)
     S3a : the converse
Checker note: comparing the generic CwF's names (CwFFv.E at this instance) with the raw names of
CPshFibC costs about 3 s per comparison; the steps are named so that each compares once, FVr is
identified with FVd by the generic fvDef (not by unfolding), and the file is split in two.

### Lemma 16's invariance: a uniform equivalence structure is invariant under an internal homotopy

Checked, no new axioms.
  CwFKrInv.KrInv (generic CwF layer)  krTr : El (Id(r , r')) -> El (Kr r) -> El (Kr r')  (CwFTr.trP in
                           CwFQP's universal family K1);  krHt : the same from a homotopy, by NF
  CPshMapC.MapCOf[C].M[G, Y, X]   toEl : CMap[G, Y, X] -> CEl[G.Y, X[p]] ;  ofEl : the converse (CPshFvC's al is
                           ofEl (bod r)) ;  of-to , to-of ;  cmap-ext ;  base: AlOf, ElOf, pmap-ext
  CPshInvC.InvCOf[C]
     Inv[G, X, Y, r, r', H].inv : UTriv (G.X) HP[al r].PC -> UTriv (G.X) HP[al r'].PC,
                           H an element of Id(bod r , bod r') over G.Y
     InvM[G, X, Y, f, g].inv H : the same for CMaps f , g and H : CEl[G.Y, IdC[G.Y, X[p], toEl f, toEl g].IdT]
     Zig[G, X, Y, f, m, g].inv Hq Hp : the zig-zag form, Hq : f ~ m, Hp : g ~ m (CwFPth.symM / transM)
The homotopy is INTERNAL (an element of the C-level Id), so its C-naturality is part of the datum.
For Lemma 16 (uniform form) it remains to instantiate Zig at f = D tau_A pulled back along tau_G,
m = the middle map, g = tau_DAC, with Hq , Hp from CPshNF.LineYC at Lemma16's lines q , p (C-natural by
LC.qC / LC.pC): canonicity-45.

## NF on CFibCwF (canonicity-c2, 2026-11-11)

Checked: CPshNFC.NFCOf[C].nf, naive function extensionality in the CwF of uniformly fibrant C-types,
in the argument shape of FibNF.nf (Pi = CPshPiFibC.FPiC.SPi, Id = CPshIdJ4.PIdJ): the raw
CPshNF.NFC.nf applied to the function of h.  No new axioms.

## D is stable under C-substitution (canonicity-c2, 2026-11-11; for Theorem 29)

Checked, no new axioms (fe; univ only through V's extensionality, in IdV-ext = CPshPi.propV-ext):
  CPshDSub.DSubOf[C]
    S[De, G, s].DSb       D s : CSub[D De, D G], s applied to every value of a family
    DSb-id, DSb-o         D of the identity, D of a composite
    S[De, G, s].tau-nat   D s o tau = tau o s
    El[G, A, el].DEl      D on elements: CEl[G, A] -> CEl[D G, D A]
  CPshDSubT.DSubTOf[C].T[De, G, s, A]
    DT-sub                (D A)[D s] = D (A[s])  as C-types over D De
    DAC-sub               (DAC A)[s] = DAC (A[s]) for DAC = (D A)[tau] over the context (DAG-is: it is Cor15's DAC)
Method: the index of a family does not mention the context, so D s reindexes nothing.  For the
types, the value component has the same code on both sides; the three equation codes are Pi codes
over the same indices of IdV codes with equivalent truth values (the reading rB of CPshL.SC commutes
with the actions and is injective over a point), hence equal; the transport keeps the values (sig0).
Not here (left for Theorem 29's design note): D of a context extension, D(G.A) vs DG.DA.

## Plan: Prop 34 (propositional truncation is computed levelwise), design note (canonicity-c2, 2026-11-11)

No code.  Source: jonas.pdf §5 (Theorem 21 to Prop 36) and §2.3.

Statement.  Naturally in Γ, for A in Ty^DT(Γ): El^T(UΓ, ∥UA∥) <-> El^DT(Γ, ∥A∥).  With the ruling
T = id (sag-model README: no choice is used) this is El^Fib(UΓ, ∥UA∥) <-> El^D(Γ, ∥A∥) for A D-modal,
which is DUALITY.md's premise S3.8 (`E3.TrS.prop34-l / prop34-r`), stated there in reading (A) over the
premise S3.7 (a truncation Tr of the model, stable under substitution).

What the paper's proof uses, and what we have.
1. §5.1 (Theorem 21, Lemmas 23-25: T lifts levelwise, Assumption 4 on C1): VACUOUS for T = id.  Nothing
   to do; Assumption 4 is not needed.
2. Theorem 29 (DT is a descent data operation on PSh(C)Fib; modal types).  For T = id: D τ_A and τ_DA are
   equivalences in PSh(C)Fib, for A fibrant.
   HAVE: D on contexts and types and τ (Cobar), Lemma 12 in the paper's form (Lemma12F.lemma12F: D of a
   levelwise fibrant type is uniformly fibrant) and its trivial half uniform (lemma12U), Lemma 14, Prop 13
   and Cor 15 in the internal (uniform) form (prop13U, cor15U: so D τ_A is done), Lemma 16 levelwise with
   the C-natural zig-zag, Prop 17 abstractly (duality-presheaf).
   MISSING: (a) Lemma 16 in the uniform form = the invariance statement (uniform EquivOp is invariant
   under a C-natural homotopy), planned through the S3 bridge (both directions checked at the raw level:
   CPshContr, CPshURel, CPshFibMaps, CPshIdExt, CPshFibC) and its packaging on CFibCwF, which waits for
   CPshIdJ; (b) D as a LEX OPERATION on CFibCwF, i.e. its action on C-substitutions and elements and
   (DA)σ = D(Aσ); I found DC (contexts), DT (types) and Prop13's DF (maps of types) in the tree, but no
   stability of D under C-substitution: to check with canonicity-45 / write.
3. Lemma 31 (RA is D-modal for A levelwise fibrant over UΓ), Lemma 32 and Prop 33 (for T = id, Prop 33 is
   Lemma 31).  HAVE: R on contexts and types with its reindexing C-action and Lemma 9 for trivial
   fibrancy (CPshR), the unit η on contexts (CPshR.EU), Lemma 14.
   MISSING: (c) R on fibrant types (UFib of R A from levelwise Fib of A; the C-action being reindexing,
   as lemma9 but for compositions); (d) the adjunction on elements El(UΓ, A) = El(Γ, RA) and on maps and
   homotopies (R commutes with the identity type up to the needed map); (e) "a type whose unit has a left
   inverse is modal" for a descent data operation, a generic CwF lemma (not found in duality-presheaf).
4. Truncation in both models, with the universal property into (modal) propositions.  This is the real
   gap.
   BASE.  unit/core has CTrunc* (32 files, 2811 lines): the truncation presheaf for the poset model with
   inc, the seeded extension, paths between every pair, the recursor, dependent elimination into fibrant
   propositions with the inc rule.  Its own header says: "composition on truncation and substitution
   stability of the type construction remain unproved.  This is not yet a complete CwF former", and
   LEDGER.md row 8 says CTrunc* was built for the old cofibrations and is not reused; replacement
   (cavrep Construction 53) is "todo in Unit".  So the base does NOT have ∥-∥ as a fibrant type former
   stable under substitution over PosFull, which Prop 34 needs on its left side.
   C-LEVEL.  Needed: Tr A : CTy[Γ] for A uniformly fibrant, with (i) its type at x; if the base
   truncation is strictly functorial in maps of types over maps of contexts (CTruncMorphism / CTruncNat
   suggest it is, by construction), then Tr A at x := the base truncation of A_x and the C-action is that
   functoriality, with tE-id / tE-o strict (they cannot come from the eliminator, which gives them only up
   to a path, and truncation's fibres are sets of codes, not strict propositions); (ii) uniform fibrancy:
   the base composition of the truncation commutes with the C-action; (iii) inc, the proof of
   propositionality, and elimination into uniformly fibrant propositions as C-elements, natural in C;
   (iv) stability under C-substitution (S3.7), from the base's.  Then the truncation of the inner model:
   ∥A∥^D := D (Tr A) (LEDGER row 8: "image in the inner model = Σ b. D‖fib b‖"), with elimination into
   D-modal propositions.
5. Prop 34 itself, given 2-4.  Left to right: U∥A∥ is a proposition with a map from UA, so an element of
   ∥UA∥ makes U∥A∥ contractible levelwise; Lemma 12 (lemma12U: D of a levelwise trivially fibrant type
   is uniformly trivially fibrant) and the modality of ∥A∥ give a centre.  Right to left: by 3,
   El^Fib(UΓ, ∥UA∥) <-> El^D(Γ, R∥UA∥); R∥UA∥ is a modal proposition; the map A -> RUA -> R∥UA∥ and the
   universal property of ∥A∥.

Size estimate (T = id; lines of .seg, by comparison with what was written for Π and the bridge, about
3500 lines in 20 files).
 - 2(b) D as a lex operation on CFibCwF, and Theorem 29 packaged: 300-600, after CPshIdJ and the bridge's
   packaging.
 - 3(c)-(e) R on fibrant types, the adjunction, Lemma 31 / Prop 33: 500-800.
 - 4 C-level truncation over a base truncation given as an interface (type former with strict
   functoriality, fibrancy, inc, is-prop, elimination, strict substitution stability): 600-1000; the
   inner-model truncation D . Tr with modal elimination: 200-300.
 - 5 Prop 34: 300-400.
 Total 2000-3000 lines WITHOUT the base truncation.  The base truncation itself, as a complete fibrant
 former over PosFull's cofibrations with strict substitution stability, is at least as much again
 (CTrunc* is 2811 lines and stops before composition and substitution stability), or the general
 replacement of cavrep §3.4, larger still.

Options for the decision.
 (P1) Prop 34 CONDITIONAL on one named base-level premise: a record "TruncStr" on the base's fibrant CwF
      (the interface of point 4, BASE) replacing the two C-level premises S3.7 and S3.8 by one premise
      about the cubical base only.  Everything else (2-5) proved.  About 2000-3000 lines.
 (P2) Also build the base truncation (finish CTrunc* over PosFull: composition, substitution stability,
      strict functoriality).  A separate project of the size of this whole stage.
 (P3) Defer Prop 34: keep S3.7 / S3.8 as semantic premises, and spend the effort on finishing the
      bridge's packaging, the invariance statement for Lemma 16 and Theorem 29 (items 2(a), 2(b)), which
      Prop 34 needs anyway and which also close the uniform form of Lemma 16.
 Recommendation: (P3) first (it is a prerequisite of the others and waits only for CPshIdJ), then (P1).
 Dependencies on other sessions: CPshIdJ (canonicity-45) for 2(a); whether D's stability under
 C-substitution exists (to ask canonicity-45, the author of Cobar.seg).

J and the Id structure of the CwF of fibrant C-types (canonicity-45,
2026-11-11).  `CPshJNatT.seg`: `JNatTOf[C].JNatT[Gc, Dc, CM, y, x, f, jd',
jd, prEq, lamEq, psiEq, kC', kC, cu, d', d, dEq].jnat` — J commutes with
the C-action, generic: a C-context Dc over Gc, a C-type CM over Dc, J-data
(PosJNat.JD) at y and x commuting with Dc.act y x f, compositions with the
body of UComp at (y, x, f) in place of PosJNat.JNatG's kopMv, starts with
dEq; the type map CM.tE over Dc.act replaces JNatG's substitution.
`CPshIdJ4.seg`: `IdJOf[C].PIdJ : CwFId.SwanId[l+, CFibCwF].IdJStr`, from
twelve small files: Ja (IdT := (IdC.IdT, idCl), IdT-nat := INat.law, rfl :=
reflC, DRC = SwanId.Der of the record, the derived context at x is
PosIdYJ's DY on the nose), Jb (the record's centre at x = FibIdCen.DR.cen,
FibIdRd.elTr with one path of codes on both sides), Jc / Jc2 (the record's
upS at x = DR.upS, both the lift at a coerced second component, three
one-time coercions into the base's spelling), Jd (PosIdYJ's J-data commute
with the C-action: prEq by A.tE-pt, lamEq by readings through io / oi,
psiEq), J1 (J := PosJNat.JJ at the record's context for the Yoneda data,
the start transported once to PosIdYJ's centre; el-nat by JNatT; J-beta by
JJ.beta read back along cenEqY with FibId.betaTr), J2 (rfl-nat: RflNat.pt
at each x; cen-nat: CN.ptR at each x through cenEqC / upSEqC), J3 / J3p /
J3b / J3l / J3c (J-nat: PosJNat.JNatG at each x for the record's upS read
at x, with the base's JNt commutations restated once each; the J's of
JNatG are the instance's by refl).  Rules learnt (ten-second rule): never
rely on unfolding inside module-instance arguments — spell them literally
(no local abbreviations: `(DRC.Dx G A a0).ob x`, the substituted motive
written out) so that two instances meet syntactically; every change of
spelling is one opaque lemma (2–6 s each) and a file holds at most two.
Negative test: J-nat's pointwise step by refl fails.

## Plan: Theorem 29 (T = id), design note (canonicity-45, 2026-11-11)

No code.  Source: jonas.pdf §2.3 (Definition 4, footnotes 7-8), §4.2.2 (Lemmas 14, 16,
Corollary 15), Theorem 29; consumer: unit/sag-model/DUALITY.md rows S2.2-S2.4, S2.6, i.e. the
record `DS` of sag/duality-presheaf/T2.seg.

1. The statement we instantiate.  With T = id (sag-model README) the lex operation DT is
   D-bar A := (D A)[tau_G] (the paper's "DA := (DA)alpha", §2.3), on the CwF of uniformly
   fibrant C-types CFibCwF.  Theorem 29 then says three things.
   (i)   D-bar lifts to fibrant types (the paper's Prop 26, which for T = id is Lemma 12):
         A uniformly fibrant over G  =>  D-bar A uniformly fibrant over G.
   (ii)  D-bar is a descent data operation (Definition 4): D-bar tau_A and tau_{D-bar A} are
         equivalences for every A in Ty^Fib(G), where tau_A : A -> D-bar A is the unit.
   (iii) The "furthermore" (is-equiv(pi_A) <-> is-equiv(tau_A) x is-equiv(theta_UA)) is the
         tautology is-equiv(tau_A) <-> is-equiv(tau_A) x 1 for T = id, and "DT-modal = D-modal"
         is a definition.  Nothing to check; the modal types are Ty^D(G) = {A fibrant, tau_A an
         equivalence}.
   Definition 4 presupposes a LEX OPERATION, which the paper obtains from the pointed
   pseudomorphism (footnote 8: D-bar on maps of types as D-tilde b := (D b)[down][alpha+]).
   We take the lex operation DIRECTLY, with the action on maps of types given levelwise
   (Prop13U.DfC: D f as a CMap, f applied to every value), so the comparison map
   <Dp, Dq> : D(G.A) -> DG.DA of a pseudomorphism (footnote 7) is NOT needed for Theorem 29.
   Neither is Lemma 11: its path-type half exists in the form Lemma 12 uses (Lemma11L, D of the
   lines), its product half is needed only for the inner model's Pi (ModPi, S2.8), see 5.

2. The definition, as a record.  There is none in the tree (the only `Descent` is étale-flat's).
   Proposed: `DescentOp` on CFibCwF, with the bridge's internal equivalence of a map of types
   (S3a_C / S3b_C final form, COBAR.md "The S3 bridge": a centre and a contraction of
   FVc = Sigma_y Id(f y, x) over G.X, equivalently EquivOp at each x + CUnif) as the notion
   IsEqT.  Fields:
     DT      (G) (A : STy G) : STy G                                   D-bar on fibrant types
     DT-sub  (DT A)[s] = DT (A[s])                                      as STy (Cl included)
     Dm      (m : Map G A B) : Map G (DT A) (DT B)                       D-bar on maps of types
     eta     (A) : Map G A (DT A)                                        tau_A
     eta-nat eta (A[s]) = (eta A)[s]  (transported along DT-sub)
     desc1   (A) : IsEqT G (DT A) (DT (DT A)) (Dm (eta A))
     desc2   (A) : IsEqT G (DT A) (DT (DT A)) (eta (DT A))
   Map G A B = CEl[G.A, B[p]] (T2's Der.Map).  The consumer record `DS` (T2.seg, on a PCwF;
   CFibCwF qualifies: isSet-CTy + isSet-UFib give isSetTy) asks for MORE than Definition 4 and
   not for desc1 / desc2: DC, DSb, tauC, tau-nat, DT (the family action over DC G), De, DT-sub,
   De-sub, tauT, hc-tau, Modal := IsEqT tau_Q, Modal-sub, DT-fib, D-eq, isoT, restr-eq, post-eq.
   Theorem 29 proper is the DescentOp instance; the DS instance is the natural next packaging
   (its D-specific fields are listed in 4(B)); desc1 / desc2 feed Prop 34 (Lemma 31 / Prop 33)
   and the inner model.

3. What is in the tree (checked).
   D on contexts / types / substitutions / elements, functoriality, tau natural (Cobar, CPshDSub:
   DSb, DSb-id, DSb-o, tau-nat, DEl); (D A)[D s] = D (A[s]) and (DAC A)[s] = DAC (A[s]) (CPshDSubT:
   DT-sub, DAC-sub); D of a levelwise fibrant type uniformly fibrant over D G (Lemma12F.lemma12F)
   and the trivial half (lemma12U); tau_A as a CMap (Cor15.tauA); D f as a CMap (Prop13U.DfC);
   Prop 13 uniform (Prop13U.prop13U: EquivOp at each x + CUnif of the fibre ContrOps of D f over
   D G, for U f an EquivOp); Cor 15 uniform (Cor15.cor15U: the same for D tau_A over D G); Lemma
   16 levelwise (Lemma16.lemma16: EquivOp of tau_DAC at each x by the zig-zag K and Lemma 12 at
   DAC); the raw bridge both ways (CPshContr C1 / C2, CPshURel, CPshFibMaps, CPshIdExt, CPshFibC).

4. Missing pieces, with sizes (lines of .seg; each < 10 s per file by the spelling rule).
   (A) For Definition 4 (Theorem 29 proper).
   M1  DT: D-bar A as an STy: (DAC A.1, clSubU G (D G) tau (DCTy) (lemma12F from A.2 read
       levelwise)).  Lemma12F takes a levelwise fibration structure al; A.2.1 x gives it.  60-100.
   M2  DT-sub on STy: DAC-sub for the type, isSet-UFib / ufib-eq for the closure.  40-60.
   M3  eta as a Map (CEl[G.A, (DT A)[p]]) from Cor15.tauA (a CMap), and eta-nat: tau_A[s] =
       tau_{A[s]} (missing: like DAC-sub, the value component unchanged, equation codes by
       IdV-ext).  Needs the generic Map <-> CMap conversion of the packaging (III) (a Map read at
       x is a PMap over G_x, natural in C by el-nat; and back): if c2's packaging does not
       provide it, 80 lines here.  100-150 + conversion.
   M4  Dm: from Prop13U.DfC (D f as a CMap over D G) pulled back along tau_G (a CMap pulled back
       along a C-substitution: missing, 40-60), then CMap -> Map.  80-120.
   M5  desc1: cor15U is a uniform EquivOp of D tau_A OVER D G (Prop13U's shape over
       HPD.GB = (D G).D(DAC)); D-bar tau_A is its pullback along tau_G.  Missing: a uniform EquivOp
       (Unif.CUnif) is stable under pullback along a C-substitution (the fibre C-type and its
       ContrOps reindexed; the CUnif condition is pointwise, so this is a restatement).  60-100.
       Then the bridge S3a (c2: SA.utFV, C1) and the packaging (III) give the internal form.
   M6  desc2: Lemma 16 in the UNIFORM form = c2's invariance statement (uniform EquivOp invariant
       under a C-natural homotopy, applied to K : D-bar tau_A ~ tau_{D-bar A}), then S3a and
       packaging.  c2's item; what Theorem 29 needs from it is exactly: UTriv of the fibres of
       tau_{DAC} over G.DAC (Prop13U's shape), given cor15U's for D-bar tau_A and Lemma16's
       levelwise K.  Sent to c2 with this note.
   M7  The record DescentOp and the instance.  60-100.
   Total (A), my side: 500-700 lines, after the packaging's Map <-> CMap and the internal IsEqT
   are fixed by c2 (I will write against the raw form, centre + contraction of FVc, if the
   packaging is not there when M5 is reached).
   (B) For the DS instance (Tier 2 consumer), beyond (A).
   M8  De-sub (the left square of Lemma 67): (DEl a)[D s] = DEl (a[s]) transported along
       DT-sub; same method as DSb-o / DT-sub (values unchanged, equations props).  80-120.
   M9  hc-tau: restricting DEl a along tau_G is tau_A's action on a: strict by Definition 10
       ((Da)(tau gamma)_{f}(i) = a(gamma f) = (tau_A a)_{f}(i)), one el-ext.  40-80.
   M10 Modal-sub: IsEqT stable under substitution (raw form: the centre and contraction of FVc
       reindexed, with CPshFibC's FVc[s] = FVc of the reindexed map) + eta-nat (M3).  60-100.
   M11 DT-fib = M1; tau-nat, DSb, DC, DT, De, DT-sub exist.
   M12 D-eq (Prop 13 for a levelwise equivalence of CONTEXTS T -> G, output an internal
       equivalence of contexts IsEqC): a context map is not a map of types; either re-run
       Prop13's PSI on contexts (D of the homotopy fibre of s, moved from lemma12U) or reduce to
       Prop 13 over the terminal context (a CCtx as a CTy over 1).  To measure: 200-400.
   M13 isoT (a map of types with a two-sided inverse is an IsEqT): at x the base's quasi-inverse
       argument (Cor15's ef through QinvEq.QE), uniform in C, then S3a.  150-300.
   M14 restr-eq, post-eq (S2.2, Rijke 13.4.1 through PSh(C)(1, -)): from the internal
       equivalence to an equivalence on El(D, -): from the uniform centre of the fibre of f at
       each point, the inverse on elements, C-natural by uniformity; the homotopies likewise.
       150-300 each.  These are bridge statements, not D's; to assign.
   Total (B): 900-1500 lines; M12-M14 are the uncertain ones.
   (C) Not Theorem 29 but adjacent: the comparison <Dp, Dq> : D(G.A) -> DG.DA is an ISOMORPHISM
   on the nose (Definition 10: a family of pairs with componentwise equations is a pair of
   families; Sigma commutes with the weighted limit), 200-300 lines when the inner model's Sigma
   (D-tilde B := (D B)[down][tau+]) or the paper's pseudomorphism form is wanted; the product
   half of Lemma 11 (D(Pi A B) = Pi (D A) (D-tilde B)) for ModPi (S2.8), 300-500.  Neither is
   needed for Theorem 29 or for the DS instance.

5. Order.  M1, M2 (immediately; no dependency) -> M3, M4 against c2's Map <-> CMap or my own
   conversion -> M5 (Unif pullback) -> M7 with desc1; desc2 when c2's invariance lands -> then
   (B) M8-M11, M12-M14 to assign.  Negative tests: M1 (drop the levelwise structure of A from
   lemma12F's input: must fail), M5 (break the CUnif pointwise condition), M7 (desc1 with the
   wrong unit, eta (DT A) in place of Dm (eta A): must fail).

Theorem 29 part (A), files (canonicity-45, 2026-11-11): `CPshDT` (Dbar A = (D A)[tau], Dbar-sub =
DAC-sub, Dbar-fib = Lemma12F along tau, eta = Cor15.tauA, record DescentOp on the raw CwF with Cl as a
predicate: maps of types are Prop13's CMaps and "f is an equivalence" is a UTriv of Prop13.HP[.., f].PC);
`Prop13U.DfOf[C, G, A, B, f].DfC` (D f as a CMap, no fibrancy hypotheses); `CPshMapSub.subCMap` (a CMap
pulled back along a C-substitution, reading lemma MS.rd); `CPshUTrivSub.subUTriv` (a UTriv pulled back:
CFibSub.moveContr at x, kopMv, side-extH); `CPshEqSub.subEqU` (a UTriv of HP pulled back: the base's
CHSub / CHFibCart at x, the fibre type of the substituted map being HP's type of the pulled-back CMap
on the nose, so no comparison of fibre types; mSC: HCart's comparison map commutes with HP's action).
Known gap, recorded on request of 4e: the paper's Lemma 12 is "naturally in Gamma", i.e. the fibration
structures of D A are stable under substitution on the nose; not proved (nothing uses it), which is why
the record is on the raw CwF.  Negative tests: one step of nat / res dropped in each pullback file fails.

THEOREM 29 (T = id) CHECKED (canonicity-45, 2026-11-11): `CPshL16U.L16UOf[C].PDesc : CPshDT.DTOf[C].DescentOp`,
i.e. D-bar A = (D A)[tau] is a descent data operation on C-types (Definition 4): Dt = Dbar, Dt-sub =
DAC-sub, Dt-fib = Lemma 12 along tau, unit = tau_A, Dm f = (D f)[tau] (CPshDesc.Dm, from Prop13U.DfOf and
CPshMapSub), desc1 = Cor15.cor15U pulled back along tau_G (CPshDesc.desc1, by CPshEqSub), desc2 = Lemma 16
uniform (CPshL16U.L16I.desc2): Lemma16's lines p, q (the double readings LN2.mwe at the weights ML / MR,
natural in the base by mwe-act, with the ends E0 / E1, natural in C by MWC) are made internal homotopies
of the CwF of fibrant C-types by CPshNF.LineYC (module Ln, generic in the line), and canonicity-c2's
CPshInvC.Zig moves desc1 along q . p^-1; the one identification needed (D-bar tau_A at x is Lemma16's
dTau x) is alEq, by the reading lemma CPshMapSub.MS.rd.  File times: CPshDesc 1.1 s, CPshL16U 6.4 s.
Negative test: dropping the C-naturality step mwc in Ln.UC fails.

## The base's propositional truncation (canonicity-c2, 2026-11-11; SIMPLIFIED.md item 1)

In the tree: core's CTrunc* (SAG 8.3: normal forms inc / seeded ext, a V-coded type, the seeded
extension algebra = "proposition", a path between any two elements, recursor, initiality,
functoriality, elimination into fibrant propositions) read at the PosFull base: 21 files are core's
(symlinks), 9 are adapted copies deciding membership in a cofibration through the base's interface
(CTruncRaw.dec / toL / ofL / decideL, decide-cong2).  They still use one definitional fact of the
instance: Lands (pre h Q) g is Lands Q (h g) by computation.
CTruncPush.Push[D, G, s, P].pushTy : the pushforward s_* P of a type along a map of contexts
(families over the points of D above x.h, natural; restriction reindexes), push-eq, ov-irr, at.
CTruncPushAlg.PushOp[D, G, s, P].Op[kP].op : a seeded extension operation on s_* P from one on P
(Side form: PS.side the projected side, kop, Sd.res = kside, Un.res = kunif); PushAlg.algebra in the
algebra form of the recursor.  DONE.
CTruncSubOp.SubOp.op : the operation is stable under substitution.  CTruncPushAdj.Tp / Ut : transpose
and untranspose for s_*.  CTruncSeed.Seed.seed : ||A||[ev src] -> ||A||[ev tgt] over the lines of G
(transport of A, inc, transpose, the recursor, untranspose).  CTruncFib.OpRC.rc : the operation as a
relative contractibility structure of B[p] over G.B;  CTruncFib.TrComp.comp : the composition of ||A||
(CMove.Mv to that structure at (target end , seed));
CTruncFib.truncFib : CL.Lines[G, A].Fib -> CL.Lines[G, ||A||].Fib.   FIBRANCY DONE.
Strict stability Tr0-nat is DROPPED (ruling 4e).
CTruncCwF.TrOf[G, A]: Tr0 : FC.STy G; incE (the unit as an element over G.A); rcTr / contrTr (over
G.Tr0 A the weakened truncation is contractible: ContrOp, and an element of the internal isContr);
El[B, p].elim / beta (core's elimination into fibrant propositions).   ITEM 1 DONE.

## Prop_U and closed codes (canonicity-c2, 2026-11-11; SIMPLIFIED.md item 2)

Done (2a): CClosedCode.Closed[T0, c]: code G (the constant code of a closed level-a fibrant type over any
context), DecT G (its decoding in FibCwF[a, a+]), toDec / fromDec (same elements), tg / dec-nat (the
decoding's action is T0's), elUp.  A truncation over a varying context has NO code (it would force strict
stability); only closed ones do.
Plan (2b), for T = the level-a truncation of a closed type P0: Dec is a proposition, has the unit, and
eliminates into LARGE (level a+) propositions over G.  Two levels meet here (codes are level a, the
ambient CwF is level a+).  Route: (i) the contractibility structure of Dec[p] over G.Dec at level a+ by
CMove.Mv (it is level-polymorphic) from the level-a OpRC.rc; FibContr gives the internal isContr;
(ii) elimination into a large proposition B over G: the level-a+ truncation T+ of the lifted type has
core's recursor into B's algebra; a map Dec -> T+ is the level lift of raw trees (liftRaw: structural
recursion Raw at level a -> Raw at level a+, both over terminal contexts; it commutes with restriction by
a standalone induction, hence preserves Good); compose.
Plan (2c): Prop_U := Sigma (c : Cod) isProp (Dec c) on FibCwF[a, a+]; propositional extensionality from
the universe's univalence in the form available (ContrOp form if the S4 bridge gives no more).

Step 2a of SIMPLIFIED.md (canonicity-45, 2026-11-11): the syntax and its codes.  `CSyntax` (Tier 1's
expressions Expr (Fin n) over a metatheory ring, equations, presentations; the derivation trees of the
congruence of a presentation with ends, Valid and Proof t u; proofs as a congruence: refl / sym / trans,
sumP / mulP, the ring laws and the equations as proofs; relative presentations, the concatenation x.u,
the embedding of generators, renaming of terms and of derivations with ends, validity and proofs
preserved).  `CExprCode`, `CDerCode`: V-codes of Expr (Fin n), Tree, Valid d and Proof t u by pack /
unpack into WCode's W-type (shapes = tag + payload, arities by Empty / Top / Bool), roundtrip, encInj;
sums through the pair over Bool; propositions by encProp.  `CRelCode`: the congruence in the form the
Voevodsky quotient takes it (canonicity-c2's ruling: only CLOSED truncations have codes): for metatheory
x, t, u, the constant type of Proof_x t u over the terminal context (CConst at level a), its truncation
there (CTruncCwF.Tr0 over nilP), its code over every context (CClosedCode) and the propositionality of
its decoding (CClosedProp).  Ring.seg is symlinked from sag/polynomial.  The pilot's HRing now states
"Id is a proposition" internally (El G (Id_{Id x y} p q)); its external form was unsatisfiable in the
model (4e), the same mistake as reading a metatheory truncation into El G (Id x y).  Check times all
below 0.3 s; the negative tests of these files are the checker's own verification of injectivity.

## The Voevodsky quotient (canonicity-c2, 2026-11-11; SIMPLIFIED.md item 3): design, approved by 4e

Done toward it: CwFPropU (isProp, PropU, PropExtTy = the hypothesis, a module parameter), CwFPropExt.propExt
(the hypothesis from UaContr, generic; base instance of UaContr = S4, open), CwFTrunc.TruncAt (truncation
without stability: Tr, inc / incS, trProp, elim), and for canonicity-45's relation the coded closed truncation
(CClosedCode, CClosedProp, CTruncLevel.ElimUp).
Plan, generic in a CwF with Pi, Sigma, Swan Id, NF, Un, parameters pe : PropExtTy and tr : TruncAt:
  data  A : Ty G, r : El G (Fun G A PA) with PA = Fun G A (PropU G) (the relation, curried), and refl / sym /
        trans of the decoded relation as elements.
  K = G.PA (variable P); over K.A[p]: ra = app (wkF (wkF r)) q, Pv = the weakened variable;
  S = Sigma (A[p]) (Id (PA weakened) ra Pv) over K;   Q = Sigma G PA (tr.Tr K S).
  ONE truncation over ONE context K; all uses substitute that type (inc is an element over K.S).
  cls : El (G.A) Q[p] (pair of ra0 = app (wkF r) q and inc at (a , refl), through Sig-ov and the substitution
        extS p ra0 : G.A -> K);
  cls-eq (pe pointwise + NF + trProp), eff (Id of first components applied at b, transport in Dec, refl of R),
  surj (a second instance of Tr, over G.Q), isSetQ by the SHORT route (4e): Q embeds in PA since its second
  component is a proposition, so only "PropU is a set" (Hedberg-style, from pe only) and Pi are needed;
  elim into h-sets with elim (cls a) = f a as an Id, elim2, elimP (dependent, into propositions over G.Q).
  Base instance of TruncAt: CTruncCwF.TrOf (trProp from contrTr by "two elements of a contractible type are
  equal", CwFCC; elim's hypothesis from the Id form to core's Path form by FibHt.YH).
Files planned: CwFQuot (definitions, cls, cls-eq, eff), CwFQuotSet, CwFQuotElim, CTruncAtBase.  700-1,000 lines.
After Q and before GrothCB: measure S4's remaining assembly (4e), since the user wants no hypotheses.

### The Voevodsky quotient: state (canonicity-c2, 2026-11-11 evening)

Checked, each with a negative test:
  CwFQuot.Quot[.., NF, tr].Q[G, A, r]: Qt, cls (over G.A), clsG a, fst-cls (the first component of the class of
      a is r a), Rel a b = DecP (r a b), relProp, and
      eff : reflexivity -> (a b) -> El G (Id Qt (clsG a) (clsG b)) -> El G (Rel a b).
  CwFQuotEq.QuotEq[.., NF, tr, pe].E[G, A, r]: mV a (r a c for c the variable, in PropU over G.A), relV a, and
      cls-eq a b f g : El G (Id Qt (clsG a) (clsG b)), f / g maps both ways between relV a and relV b over G.A.
  Toolkit (generic): CwFMaps (USI.upId, apF, FstF, EvF with values), CwFPropPair.pairPath (Sigma with a
      propositional second component: joined first components give joined elements), CwFPropProp.propProp
      (isProp (isProp A), from NF), CwFPropU.PropU-ov.
Also checked since (2026-11-11 later):
  CTruncAtBase.truncAt: the base's truncation as an instance of TruncAt at FibCwF[a, a+] with FibUniv, FibNF;
      quot / cls: the quotient instantiated at the base.
  CTruncLevelCwF.ElimUpP: a decoded closed level-a truncation eliminates into any internal proposition of
      level a+ (CoreProp: internal isProp gives core's; ElOfN).
  CwFUnpk: G.(Sigma A B) is a retract of G.A.B (pk, pkUnpk, sect).
  CwFQuotElimP.elimP G A r P pPr h : El (G.Qt) P, for P a family of propositions over G.Qt and h over G.A at
      the class map (ClsAt.fstAt: the first component of the class at any point).
  CwFQuotEq.relV-pt a b : subT (relV a) (sec b) = Rel a b.
Open: elim into h-sets (with beta as an Id-element; built on elimP through the proposition
  T q = Sigma (b : B) Pi (a : A) (Id (r a) (fst q) -> Id (f a) b)), set-ness of Qt (Hedberg's argument on Qt
  with "pointwise equivalent first components"), elim2.  surj is elimP at P := the truncation itself.

## The base at the total site (canonicity-c2, 2026-11-11; SIMPLIFIED.md item 4)

CGrothBase.GrothOf[C].GB : CBase.CB at CTotCat's TotCat (8851b7c3).  Sieves of (I, x) are sieves of I;
Lands (pre h Q) g is Lands Q (h g) by refl (lands-pre-refl), as on posets.  The interval is a PRESHEAF
of the base (ruling 4e; CB fields ivV, IvP, ivA, ptH, endS; installed in unit/core with the user's go-ahead,
1fd0fe1e), so GB needs neither a terminal object nor IC's term / bang.  Levels a vl l (0d43c526, with
canonicity-45's 03bef1e8): the internal category's objects and maps are coded at the vertical level vl, GB =
CBase[vl].CB, the interval code through TC.embV.  The fibrant CwF at the total site is the generated segment
CFibSeg[vl].FB (fibCwF-T, fibPi-T, fibSig-T, fibId-T, nf-T, contr-T, Tr0-T, contrTr-T; tools/mkseg.py).

## U, R and the truncation at the total site (canonicity-c2, 2026-11-11; SIMPLIFIED.md item 5)

G1 = GrothOf[C] (total site), G0 = GrothOf[disc] (levelwise site, canonicity-45's CDisc), fn : G0 -> G1.
  CRestr.Restr[Cs, Ds, F]      U: rC, rS, rT, rE (restriction along a functor)
  CRan.Ran[Cs, Ds, F].Ty[G, B] R on types: RB (elements are natural families b Y m p e), toR / ofR / of-to / to-of
  CTotR.TotR[C].L9[G, B]       Lemma 9: KO[al].contrR, a levelwise contraction of B gives one of R B
  CTotRFib .. CTotRFib8        RFib8[C].fibR G B fb: R of a levelwise fibration is a fibration (componentwise
                               transfer of Comp e e'; R does not commute strictly with the type of lines)
  CTotUExt                     UExt[C].FI.XG[G]: restriction of lines along fn is a bijection (extV, rho-ext,
                               ext-rho), through CDisc's factorisation Fact / Ini (vertical, then levelwise)
  CTotUFib .. CTotUFib4        UFib4[C].fibU G A fb: U of a fibration of the total site is a levelwise fibration
  CTotRSeed                    RSeed[C].SO[G, B, op].opR: R transfers the seeded extension operation
  CTotTr                       TotTr[C].Tr[G, A]: Tr := R (Tr0 (U A)), a type of fibCwF-T; contrTr (contractible
                               over itself); inc (unit); sec (a levelwise element of Tr0 (U A) gives an element)
Open: the eliminator of Tr into propositions (on demand); (vi) the retraction D (R B) -> R B and the Key Lemma.
Slowest files: CTotUFib3 6.4 s, CTotUFib4 5.6 s, CTotUFib2 4.1 s.

## D over the total site and the inputs of A_x (canonicity-45, 2026-11-11; SIMPLIFIED.md steps 4 and 2b)

Step 4, the cobar construction over the total site of an internal category C (CIntCat.IC, the displayed
record agreed with c2, with the split cleavage cart-id / cart-comp added for the cobar layer):
  CVert      the vertical category at a stage J (VCat J : SmallCat), restriction rmap of vertical maps along
             base maps (rmap-id / rmap-comp / rmap-o), the vertical part vpart of a total map (vpart-id /
             vpart-o), the total-hom calculus (TH-tr, cmpL / cmpR, vpart-eq, rmap-eq, cc-tr).
  CChainsF   the chain map of a functor between small categories (chF, with comp / drop / rx / tot).
  CChainsT   chains at a stage: head transports trCh, restriction rCh along base maps, the action's
             reindexing rxM; RR (rCh commutes with rxM up to the base's associativity), RxId / RxO (the two
             laws), tot-rCh / tot-rxM.
  CTPsh      presheaves over the total site in displayed form (TCtx / TSub); CTotCat: the total category as a
             SmallCat (c2's site for GrothCB), the projection functor, cartT / factT with the universal
             property on total homs, toP / ofP.
  CobarI     DOfI[C].DC[G]: D G (families over (n, J, u : J -> I, z, c : Ch_J n (res u x) z, i) with the
             three equations), the action along total maps (Act; natPath / facePath / Top.dEq), act-id /
             act-o through the slice paths idPath / oPath, DCtx : TCtx; the unit tau with TauNat; DS.DSub
             (D on maps).  CobarIT: DTI.DTy (D on types, as Presheaf's PTy in e-form over toP DCtx), DEl (D on
             terms).  Lemma12I: UD.uf / UA.uf, the uniform face equations at the total site.
  Pending there: Lemma 12's second half, Lemma 14, Prop 13, Cor 15, Lemma 16 need the fibrancy layers at the
  total site (CPartial, CLine, CFill, CMove, CEquiv, CHtpyOps, CFibSub and the packaged FibCwF, FibClL,
  FibNF, FibContr, FibHt, FibYC, FibS3 with a Path-type IdJStr), i.e. c2's interval-presheaf CB.  The
  levelwise site is the discrete C0 once GB needs no terminal objects (C0+ otherwise).
Step 2b, the inputs of the presented algebra A_x for the Voevodsky quotient (CwFQuot.Quot.Q at nil):
  CConstLam  metatheory families over a constant type as elements: pack / pack-beta / packN (presheaf
             level), lamC / lamC-beta (fibrant CwF, Fun (Delta E) B through app), constOf (elements of
             Delta E over nil are constants).
  CRelPack   PropOf (isContr of the weakening -> PU.isProp); Rel[R, encK, x]: Tm = Delta Term_x at level a+,
             ct t, the relation r : Fun Tm (Fun Tm PropU) packaging CRelCode's closed codes with their
             propositionality, r-beta, relT-ct (Rel (ct t) (ct u) = Dec (code t u)), reflR for eff.
  CTermEval  Eval[R, x, G, Rg, phi, .., val]: ev of terms into an h-set ring with a coefficient homomorphism,
             Resp[hyp].resp / evP (derivations to Id-elements).
  Waiting on c2: elim (closed shape, with beta), elim2, elimP (internal), set-ness of Qt, and the
  elimination of Dec (code t u) into a level-a+ proposition (ElimUp in CwF form); then the ring structure of
  A_x, its universal map, and C's morphisms.

## The internal category C of presented algebras (canonicity-45, 2026-11-12; SIMPLIFIED.md step 3)

Construction 39 at the base, the vertical level vl = a+ (CIntCat[a, a+].IC), objects constant.
  CPresCode  PresCode[R, encK].presV : V[a] with Ix presV = CSyntax.Presentation on the nose (lists of
             expressions coded as well-founded trees, as CExprCode codes expressions).
  CMorX      MorOf[R, encK, pe, addO, mulO]: Fn[s, t].MorV J, the maps of algebras A_s -> A_t at the stage
             J: the fibre of the internal Fun Q_s Q_t at J (a family over the slice with its naturality)
             and Hoefer's data for add, mul (binary) and the constants phi r (zero = phi 0, one = phi 1;
             neg = mul (phi (-1)) is derived), valued in the Id fibre AT THE IMAGE POINT, each with its
             naturality.  Fn.res (the hom presheaf), Idn.idM', Cmp.cmp (composition, the naturality of
             the composed data through tact-irr / subst lemmas), Fn.mExt (maps with equal families are
             equal: the naturality parts form a proposition), Fn.rx / rxEq (reindexing along slice maps),
             CmpF.cmpFP (composition of families).  addO / mulO are module parameters (CAlgX.Ops from
             c2's elim2).
  CMorXC     CatOf[..].IC : CIntCat[a, a+].IC: homD J I u y x = Fn[x, y].MorV J (C is the opposite of
             the algebras), res u x = x, cart = identity, fact h = h; every law by mExt on families that
             agree on the nose, idr / assoc moving the slice argument along comp-idl / comp-assoc (rxEq).
             Negative test: idr / assoc with the slice transport replaced by refl fail.
  Why the data live at the image point: the fibre of the internal type (o (h u) = h v) over the variable
  h reads h through app, i.e. through transports along the context's act-id (PresheafPi.appFun), so
  composition there is not strict; at the image point it is composition of functions.
