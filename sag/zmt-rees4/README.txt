sag/zmt-rees4: the Rees presentation with kernel-membership certificates
(milestone 1 of 2)
========================================================================

Task: doc/zmt-rees-presentation-handoff.txt, doc/zmt-rees-presentation-command.txt.
Builds on sag/zmt-weighted4 (CoefficientParts, CoefficientPolynomial,
CoefficientEvaluation4: reused UNCHANGED) and sag/artin-rees (XSpan,
Saturation, DegreeCor: reused UNCHANGED), with the rest of the tree of
sag/zmt-weighted4, all by relative links.

STATUS (30 October 2026).  Gates A-D are formalised and checked, including
the regressions.  Every ring, grading, evaluation, certificate and
decomposition is constructed; nothing is assumed except the data of the
handoff (A CFN, P_q X-homogeneous).  Milestone 2 is not started.  Not
committed to git.

Check:   ./segc sag/zmt-rees4 all                          (from unit/)
Fresh:   cd sag/zmt-rees4 && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-rees4.opens


1. FOUNDATIONS, ASSUMPTIONS, FILES
----------------------------------
All.seg is the segment Theory of sag/ (as in sag/zmt-weighted4): parameters
univ, images, surjections; fe and propUA derived.  No new axioms, no new
Theory parameter, no choice (finite choices only inside truncations: the
common degree bound of finitely many coefficients, ReesFinBound), no
excluded middle, no SAG/SQC, no resizing.  The checker is unchanged.
Decisions are made only on integers (degrees); never on elements of A.

ASSUMPTIONS of the theorems (exactly those of the handoff):
  * A a commutative set-ring, CFN K0 A (for the concrete theorems; the
    generic modules need no CFN);
  * J = (P_1, .., P_s) with P_q X-homogeneous of degree e_q: either
    P_q in B with GX.pr (pos e_q) P_q = P_q (Concrete), or P_q a term list
    TPoly A with HomDeg e_q (ConcreteT, the handoff's format);
  * a_1, .., a_t in A (t >= 0, s >= 0).

New files (560 declarations, no body-less declaration):
  ReesGenerators4       Gate A (generic): index set Fin (s+t), generators,
                        the coefficients Ev of g(aT) and their laws     101
  DegreeDecomposition4  Gate A: every element of a tower D_t is merely the
                        finite sum of its homogeneous parts              75
  ReesKernel4           Gate B (generic): certificates (cert), (certU),
                        ker phi = elimination ideal                    101
  ReesComponents4       Gate C (generic): (certX), bihomogeneous
                        components, generation                          119
  ReesPresentation4     Gates A-C concrete: the towers, CFN, DegreeCor
                        GenAt at m = 0, term lists                        90
  ReesRegression4       Gate D                                            74
  All.seg, README.txt, zmt-rees4.opens
Links: the same relative targets as sag/zmt-weighted4 and its eight own
files as ../zmt-weighted4/X.seg.  No shared or earlier file was modified.


2. THE RINGS AND THE REES MAP (Gate A)
--------------------------------------
ReesPresentation4.XRing[A,setA]:
  B = CoefficientTower[A,setA].D four = A[X_0..X_3], GX = grD four : Graded A 4 B
  (X-degree; X_k = GX.var k, X_0 the variable of the innermost ring).
ReesPresentation4.Concrete[K0,A,setA,cfnA,t,a,s,P,e,hP]:
  R  = CoefficientTower[B,setB].D t = B[U_1..U_t],  GU = grD t : Graded B t R
  cfnB = cfnD K0 cfnA four : CFN K0 B ;  cfnR = cfnD K0 cfnB t : CFN K0 R
  b j = GX.iota a_j (X-degree 0: hb).
NOTE on the variable order: the handoff writes R = A[U_1..U_t][X_0..X_3];
here R = A[X_0..X_3][U_1..U_t], the same polynomial ring built with the X
first, so that both gradings are the constructed ones of zmt-weighted4 (GX
on B, GU on R over B, ev_a = GU.ev b of CoefficientEvaluation4).  No
isomorphism with UngradedSyzygies4's S = D[X_0..X_3] is formalised.

Generic (ReesGenerators4.Over[B,setB,t,R,setR,G,b,s,P], any R graded over B):
  M = R^1 (Comb.Free[R,1]), R[T] = sequences Nat -> M (SeqPoly);
  index set Fin (s + t) (ReesJoin.join, ReesIndex.jl / jr, join-l, join-r,
    ReesSumJoin.sum-join: a sum over Fin (s+t) is the two sums);
  gens : Fin (s+t) -> Blk 2:  pgen q = P_q,  rgen j = U_j - b_j T;
  XN = XSpan.Over[R,Md,s+t,F], F i = emb 2 (gens i): N = the R[T]-span.
  The substitution U |-> bT, coefficientwise (Gate A, "compatible with ev_a"):
    EvZ m g = sum_{k <= m} ev (pr (m-k) g_k)      (T^m coefficient of g(bT))
    EvZ m = 0 for m < 0; ev = CoefficientEvaluation4.Over[..,b].ev.
  Laws: EvZ-add, EvZ-zero, EvZ-sum, EvZ-van, EvZ-X (EvZ m (T g) = EvZ (m-1) g),
    EvZ-emb1 (EvZ m u = ev (pr m u) for u in R),
    EvZ-pg   (EvZ m (c P_q) = ev (pr m c) P_q),
    EvZ-rg   (EvZ m (c (U_j - b_j T)) = 0),
    EvZ-cF   (EvZ m (sum_i c_i F_i) = sum_q ev (pr m c_q) P_q).


3. GATE B: GENERATORS, CERTIFICATES, KERNEL = ELIMINATION IDEAL
---------------------------------------------------------------
Definitions (ReesKernel4.Over[B,setB,t,R,setR,G,b,s,P]):
  Blk1 = blocks of T-degree 0 (= R), elR : Blk1 -> R, ub : R -> Blk1,
    ub-elR : ub (elR u) = u; elR (ub x) = x by definition;
  JW y = (H : Fin s -> B) * (y = sum_q H_q P_q) ;  InJ y = || JW y ||   (y in J)
  Ker x = (n : Nat) -> InJ (ev (pr n x))         (ker phi, phi : R -> (B/J)[T])
  Elim u = XN.NM (emb 1 u)                        ((J, U - aT) cap R)
  pcomb d cs = sum_{k <= d} T^k sum_i cs_k,i F_i   (explicit polynomial combination)
  Cert d g = (cs : Nat -> Fin (s+t) -> R) * (g = pcomb d cs)
  CertW u = (d : Nat) * Cert d (emb 1 u)
Form of the certificate (cert): u = sum_q c_q(T) P_q + sum_j d_j(T) (U_j - a_j T)
  with c_i(T) = sum_{k<=d} cs_k,i T^k (i = jl q for P_q, i = jr j for U_j - a_j T).
Theorems:
  cert-of d g : XN.XS d g -> Cert d g     (Ruitenburg's form -> explicit form)
  cert u : Elim u -> || CertW u ||
  hh d m cs q = sum_{k<=d} ev (pr (m-k) cs_k,q),   Hc u w n = hh w.1 (cdeg n) w.2.1
  ev-pcomb d m cs : EvZ m (pcomb d cs) = sum_q hh d m cs q . P_q
  certU u w n : ev (pr n (elR u)) = sum_q Hc u w n q . P_q              (certU)
  ker-of-elim u : Elim u -> Ker (elR u)
  elim-of-hom n x : Hom n x -> InJ (ev x) -> Elim (ub x)
     (Dif n y = y - T^n ev(y) is in N for y of U-degree n: dif-in, by
      Lower.rel-sum: sum_j low_j y (U_j - b_j T) = y - T y', and tele)
  ker-elim x : Ker x -> FinDeg x -> Elim (ub x) ;  elim-of-ker u : Ker (elR u) -> FinDeg -> Elim u
Concrete (ReesPresentation4.Concrete):
  module DC = DegreeCor.Free[R,cfnR.disc,cfnR.coh,CFN.fl K0 R cfnR,1,1,s+t,gens]
  ReesW = (Gs : List Blk1) * (AllL Elim Gs * ((u : Blk1) -> Elim u -> Mm Gs u))
  presentation : || ReesW || = DC.gen zero        (GenAt at m = 0, eliminating T)
  ker-of-elim, ker-elim x : Ker x -> Elim (ub x), elim-of-ker u : Ker (elR u) -> Elim u
    (FinDeg from DegreeDecomposition4: ker phi = the elimination ideal, both ways)
  cert, certU (as above, for every element of the elimination ideal, in
    particular for every g in Gs: gens-elim of WithGens).


4. GATE C: BIHOMOGENEOUS COMPONENTS AND (certX)
-----------------------------------------------
ReesComponents4.Over[A,r,B,setB,GX,t,R,setR,G,b,s,P,e,hP,hb]:
  prX-comb d H : prX d (sum_q H_q P_q) = sum_q prX (d - e_q) (H_q) P_q
  HX u w n d q = prX (d - e_q) (Hc u w n q)
  hom-HX : HX u w n d q has X-degree d - e_q (integer subZ (pos d) (pos e_q));
  HX-below u w n d m q : e_q = (m+1) + d -> HX u w n d q = 0      (d < e_q)
  comp n d x = value (mapE (prX d) (expr (pr n x)))      (canonical, no choice)
  BiHom n d y = (ex : Expr n) * AllE (Hom_X d) ex * (value ex = y)
  comp-bihom : BiHom n d (comp n d x) ;  comp-homU : Hom_U n (comp n d x)
  ev-comp : ev (comp n d x) = prX d (ev (pr n x))
  certX u w n d : ev (comp n d (elR u)) = sum_q HX u w n d q . P_q       (certX)
  comp-elim u h n d : Elim (ub (comp n d (elR u))) ;  comp-ker : Ker (comp n d (elR u))
  part-comps decB n x : || Bx, pr n x = sum_{d < Bx} comp n d x ||
  Generate[decB,decR,Gs,span]:
    Ix = (k : Fin (len Gs)) * (Nat * Base.Nat), cp (k,(n,d)) = comp n d (g_k)
    FC = ReesFinComb[R,Ix,cp]: InComb y = || finite R-combination of the cp ||
    gen-in k : InComb (g_k) ;  generate u : Elim u -> InComb (elR u)
Concrete: certX, comp-elim; WithGens[w].kernel-generated x : Ker x -> InComb x
  (every element of ker phi is a finite R-combination of the bihomogeneous
   components of the GenAt generators, which themselves lie in ker phi).
DegreeDecomposition4 (used for "generate"):
  Decomp B x = (x = sum_{d<B} pr d x) * (pr d x = 0 for d >= B) ; FinDeg x = || B, Decomp B x ||
  TowerDecomposition[A,setA].fin-deg t : (x : D_t) -> FinDeg x
  (BaseDecomposition, StepDecomposition: constants by pr-const, U z by pr-X,
   induction on a degree bound with PolyCoef.horner).
Term lists (ReesPresentation4.TermLists, ConcreteT):
  phiT : TPoly A -> B (c X^u |-> c X_0^u_0 .. X_3^u_3),
  hom-phiT dd p : HomDeg A dd p -> Hom_X dd (phiT p).


5. GATE D: REGRESSIONS (ReesRegression4)
----------------------------------------
J = (X_0^3) as the term list [1 X_0^3] (cubicT, cubic-hom).
OverCFN[K0,A,setA,cfnA]:
  T0 (t = 0, R = B): x0 = X_0^3: inJ0, elim0 (elim-of-hom 0), ker0, presentation0.
  T1[a1] (t = 1): x = U_1 X_0^3: hom-x (U-degree 1), ev-x : ev x = a_1 X_0^3,
    elim-x, ker-x; Cert[w]: cert13 (certX at (1,3)), hom13 (coefficients
    of X-degree 3-3 = 0), below12 (bidegree (1,2): 0), comp13-elim;
    certified : || CertW (ub x) ||; generated-x : || w, InComb_w x ||.
OverZ (ZRing, ZCFN, t = 2, a = (2,3)):
  x = 3 U_1 - 2 U_2: hom-x, ev-y, ev-x : ev x = 0 (3.2 - 2.3, ring-map laws
  and computation in Z), inJ-x, elim-x, ker-x, generated-x;
  CZ = OverCFN over Z: elim0, elim1 (a_1 = 2).
Nothing about the list produced by GenAt is predicted.
Mutation tests (restored afterwards, tree re-checked):
  rgen = U_j + b_j T                      -> EvZ-rgpos fails;
  hh without the shift m - 1             -> ev-pcomb fails;
  HX at degree d instead of d - e_q      -> hom-HX, HX-below, certX fail.


6. VALIDATION (all commands under timeout 55, from unit/)
--------------------------------------------------------
  ./segc sag/zmt-rees4 changed / all
      115 modules, 0 failed, OK (all: 2.2 s warm server; new files <= 0.10 s each)
  cd sag/zmt-rees4 ; $(cabal list-bin exe:seg) All.seg
      All.seg: 7193 declarations, 0 failed, 3.05 s, OK
      (6633 = the reused tree of sag/zmt-weighted4; 560 new)
  ... All.seg --opened : every new declaration <= 0.02 s; at most 51
      definitions opened (ReesRegression4.OverZ.ev-x: the tower and Z
      arithmetic); in the generic theorem files at most 28
      (ReesKernel4.Over.Lower.rel-atS, entrywise sums of sequences).
  ... All.seg --opens zmt-rees4.opens
      47 central declarations: "nothing else opened" for each.
  Baseline unchanged, rechecked fresh:
      sag/zmt-weighted4/All.seg : 6633 declarations, 0 failed, 2.73 s
  The checking server was stopped afterwards.


7. REMAINING OBLIGATIONS AND LIMITS (honest list)
-------------------------------------------------
Within milestone 1 nothing requested is assumed.  Limits:
  * Representation for milestone 2.  The components are elements of
    R = (A[X])[U] given by expressions with coefficients in B = D_4(A), and
    H, H' are elements of B.  zmt-weighted4's dependence theorem uses term
    lists g : TPoly D with D = A[U_1..U_t] (CoefHom, HomDeg) and coefficient
    functions on Z^4.  A conversion of a BiHom n d component into such a term
    list (coefficients of U-degree n, terms of X-degree d), and of H' into a
    term list / coefficient function of degree d - e_q, is NOT formalised;
    milestone 2 needs it (a bridge D_4(A) -> coefficient functions, e.g. by
    the PolynomialRing4Bridge pattern psi/phi, and the exchange of the two
    variable orders).
  * Only the input direction is bridged for term lists: phiT, hom-phiT.
  * Ker is "ev (pr n x) in J for every n", i.e. phi(x) = 0 coefficientwise
    in (B/J)[T]; the quotient B/J and phi as a ring map are not built.
  * The coefficients cs of a certificate have no prescribed U-degree; the
    T-degree d of a certificate comes from GenAt's witness (not bounded
    a priori).
  * "d < e_q gives H' = 0" is stated with e_q = (m+1) + d (HX-below).
  * The aliases Md, M, Seq, Sq, Blk2, S in ReesGenerators4 follow the idiom
    of Saturation.Over (they name the module R^1 and its sequences once);
    aliases re-declared in the later files were removed.
  * .opens covers 47 of the 560 new declarations.
OUT OF SCOPE (not done): milestone 2 (chart-level comparison with the
I^n-images, the finite correction from the weighted theorem, cancellation
of the evaluated g-terms), full ZMT, localisation, section lifting,
arbitrary projective dimension.
