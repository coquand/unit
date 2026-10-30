sag/zmt-rees-comparison4: the Rees-to-weighted comparison and the finite
correction (milestone 2 of the Rees presentation)
========================================================================

Task: doc/zmt-rees-comparison-handoff.txt, doc/zmt-rees-comparison-command.txt.
Builds on sag/zmt-rees4 (all six files reused UNCHANGED, by relative links
../zmt-rees4/X.seg) and, through it, on sag/zmt-weighted4, sag/zmt-syzygies4,
sag/zmt-lifting(-general) and sag/artin-rees (the same relative links as
sag/zmt-rees4).

STATUS (30 October 2026).  Tasks (1)-(4) of the handoff are formalised and
checked: the fixed finite generating list, the bridge, the chart-level
comparison and the finite correction.  What REMAINS is the construction of
the inputs of the correction (the finite-fibre sections: the sequence c_n
with its lifts and the cochains z_n, see §7) and the final ZMT certificate
assembly.  Not committed to git.

Check:   ./segc sag/zmt-rees-comparison4 all                  (from unit/)
Fresh:   cd sag/zmt-rees-comparison4 && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-rees-comparison4.opens


1. FOUNDATIONS, ASSUMPTIONS, FILES
----------------------------------
All.seg is the segment Theory of sag/ (as in sag/zmt-rees4): parameters
univ, images, surjections; fe and propUA derived.  No new axioms, no new
Theory parameter, no countable choice, no excluded middle, no SAG/SQC, no
resizing; the checker is unchanged.  Finite choices only under truncation:
the common bounds (Bu, Bx) of finitely many finite decompositions
(ReesFiniteList4.fixed, via ReesComponents4.ReesFinBound) and the
certificates of the L generators of the GenAt list (ReesCorrection4.certs,
via LaurentSyzygyLift4.fin-choice).  Decisions only on natural numbers and
integers (degrees: dich, the decidable equality of exponents inside the
reused libraries), never on elements of A.

ASSUMPTIONS of the theorems (the data of the handoff):
  * A a commutative set-ring; CFN K0 A for the presentation and the
    correction (ReesRings4.WithCFN, ReesCorrection4.Over);
  * t >= 0 values a_1..a_t in A (I = (a_1..a_t));
  * s >= 0 equations p_q given as term lists with every term of degree e_q
    (HomDeg; J = (P_q), P_q = phi p_q, M = S/J);
  * for the correction, the inputs of §5 (c, hc, lift, z, hz, hcompat).
No flatness of M over A is assumed or used; I^n M is always the image of
I^n C(S) in the quotient, never I^n (x) M.

New files (460 declarations, none without a body):
  ReesFiniteList4            (1) generic: fixed bounds, the list KG, generation  78
  ReesRings4                 (1) concrete: the rings over S, GenAt, the list      60
  ReesBridge4                (2) A[X][U] -> term lists over A[U]                   96
  ReesChart4                 (3) the quotient chart complex, I-images, factor      90
  ReesCorrection4            (4) weighted theorem applied, finite correction       92
  ReesComparisonRegression4  regressions                                           44
  All.seg, README.txt, zmt-rees-comparison4.opens
No shared or earlier file was modified (sag/zmt-rees4 rechecked fresh: §8).

ONE NAME FOR A[X_0..X_3] (ReesRings4).  zmt-rees4 builds B = D_4(A) as the
coefficient tower of zmt-weighted4; zmt-syzygies4's PolynomialRing4Bridge
builds S = A[X_0][X_1][X_2][X_3] (the ring of phi, psi, coef-eq-of-phi).
They are the same ring BY DEFINITION (the same four quotient-ring
extensions; checked by refl), but the checker identifies the two
presentations only by unfolding all four levels, once per comparison
(measured: about 3,200 definitions opened and 0.03 s per comparison of the
carriers, 49,000 and 0.5 s for one comparison of the multiplications; a
first version mixing the two names took 2-3 s per lemma).  So every ring of
this milestone is built over S: the X-degree of the tower is
GX : Graded A 4 S (one identification), its variables and constants are
X_k and cst (var-x0..var-x3, iota-cst: refl, stated once), R = S[U_1..U_t]
(CoefficientTower over S), b_j = iota a_j.  The handoff's
R = A[U_1..U_t][X_0..X_3] is this ring with the X-variables first (as in
zmt-rees4).  The 3-line concrete wrapper ReesPresentation4.Concrete
(ReesW, presentation: DegreeCor.GenAt at m = 0) is instantiated again for
this R (ReesRings4.WithCFN); the generic theorems of zmt-rees4
(ReesKernel4, ReesComponents4) are instantiated at S unchanged.
TermLists.phiT of zmt-rees4 is not used (P_q = phi p_q directly; hom-phi
is the degree statement for phi).


2. (1) ONE FIXED FINITE BIHOMOGENEOUS GENERATING LIST
-----------------------------------------------------
ReesFiniteList4.Over[A,r,B,setB,GX,t,R,setR,G,b,s,P,e,hP,hb]
  .Gens[decB,decR,Gs,gens-elim,span]   (any graded data as in ReesComponents4;
   Gs a list of elements of the elimination ideal spanning it)
  Bounds Bu Bx = (k < L -> Decomp Bu g_k)            (g_k = sum_{n<Bu} pr_n g_k,
                                                      pr_n g_k = 0 for n >= Bu)
               * (k < L, i < Bu -> QX (finN i) g_k Bx) (every coefficient of the
                                                      canonical expression of
                                                      pr_n g_k decomposed below Bx)
  FixedW = (Bu : Nat) * (Bx : Nat) * Bounds Bu Bx
  fixed : || FixedW ||          (two nested ReesFinBound.fin-bound; monotone:
                                 DegreeDecomposition4.pad, ReesComponents4.all-pad)
  KG[fw]: na = L * Bu * Bx (Rect: rows joined by ReesJoin; finN : Fin m -> Nat),
    ix : Fin na -> (k, (n, d)),  kg i = comp n d g_k  (ReesComponents4.comp),
    at k i j : Fin na,  kg-at : kg (at k i j) = comp (finN i) (finN j) g_k
    kg-bihom  : BiHom n d (kg i)
    kg-elim   : kg i in the elimination ideal;  kg-ker : kg i in ker phi
    kg-certX  : for a certificate w of g_k (ReesKernel4.CertW),
                ev_a (kg i) = sum_q HX w n d q . P_q
    kg-hom-HX : HX w n d q has X-degree d - e_q
    FK = ReesFinComb[R, Fin na, kg]  (finite R-combinations of the FINITE family)
    part-eq   : pr_n g_k = sum_{d<Bx} comp n d g_k  (n < Bu)
    gen-in    : g_k in FK;  kernel-elim : elimination ideal in FK
    kernel    : (x : R) -> Ker x -> FK.InComb x
  THEOREM finite-generation : || (fw : FixedW) * ((x : R) -> Ker x -> KG[fw].FK.InComb x) ||
Concrete (ReesRings4.Rings[A,setA,t,a,s,p,e,hp].WithCFN[K0,cfnA]):
  presentation : || ReesW ||   (GenAt, as in ReesPresentation4)
  THEOREM finite-list : || (w : ReesW) * FiniteGen(w) ||
  (decB, decR: DegreeDecomposition4.TowerDecomposition at S and at R.)
The infinitely indexed family of ReesComponents4.Generate is not used for
generation.


3. (2) THE BRIDGE  A[X][U] -> TERM LISTS OVER A[U]
--------------------------------------------------
ReesBridge4.Over[A,setA,t,a,s,p,e,hp]  (D = A[U_1..U_t] the tower of
zmt-weighted4 with GD, ev = CoefficientEvaluation4.ev, evT on term lists).
X-direction (canonical):
  flatX k : Expr_X k -> TPoly A   (words in X_0..X_3 flattened: bmp, term-bmp)
  hom-flatX : HomDeg k ;  phi-flatX : phi (flatX k e) = value e
  tlX k h hh = flatX k (expr h) :  HomDeg k, phi (tlX k h hh) = h
U-direction:
  tlU d : (n) (e : Expr_U n) -> AllE n (Hom_X d) e -> TPoly D
    (tlU 0 h = liftC (tlX d h); tlU (n+1) e = sum_j U_j . tlU n (e_j))
  hom-tlU : HomDeg d ;  coef-tlU : CoefHom n ;
  ev-tlU  : phi (evT (tlU d n e hh)) = ev_a (value e)
  for y with bh : BiHom n d y:  biT n d y bh : TPoly D with
    hom-biT : HomDeg d (biT ..)  ;  coef-biT : CoefHom n (biT ..)
    ev-biT  : phi (evT (biT ..)) = ev_a y                 (evaluation certificate)
    cf-biT  : cf (evT (biT ..)) m = psi (ev_a y) m        (coefficient functions Z^4 -> A)
  cf-ev : ev (cf_D g m) = cf_A (evT g) m  for every g : TPoly D
  (ev_a = ReesGenerators4.ev, U_j |-> b_j; ev of CoefficientEvaluation4,
   U_j |-> a_j; they correspond through phi o evT: ev-tlU.)
H' as term lists:
  dich e d : (d = e + k) or (e = (m+1) + d)   (on naturals)
  hterm e d h hh : HTerm e d h = (p : TPoly A) * HomShift e d p * (phi p = h)
    for h of X-degree d - e (tlX in the first case, the empty list in the
    second, where h = 0: Pr of negative degree);  sub-eq : (e + k) - e = k.
Not built: a map from term lists over D back to R (not needed).


4. (3) THE QUOTIENT CHART COMPLEX, I-IMAGES, THE KERNEL ACTION
--------------------------------------------------------------
ReesChart4.Over[A,setA,t,a,s,p,e,hp]; MJ = the matrix with rows p_q, no column.
JC[I,set,n] (any Cech degree I, twist n; F = HomogeneousMatrices4.Fam[MJ,..]):
  JW x  = (y : prod_q C(n - e_q)) * (x = sum_q P_q y_q) ;  InJ x = || JW x ||
  jw-zero, jw-add, jw-neg, jw-sub, jw-sm; in-zero, in-add, in-neg, in-sm, in-of
  Cong x x' = InJ (x - x')   (x = x' in the chart module of M = S/J)
  cong-refl, cong-of-id, cong-sym, cong-trans, cong-add, cong-neg, cong-sub,
  cong-sm, cong-zero (InJ x -> x = 0 mod J), zero-cong (converse)
  IJ k x = || (x' : C(n)) * Wit k x' * JW (x - x') ||
          (the class of x is the image of an element of I^k C(S), with witness)
  ij-of-wit, wit-one (I^(k+1) C in I C), wit1-add, wit1-neg, wit1-sub,
  wit1-sm (r in I, z in C(n): r z in I C(n)), ij-add, ij-sub, ij-cong
Factor[na,dd,g,hg,h,hh,fac]  (g_j of degree d_j, h_qj with HomShift e_q d_j,
  fac : coef g_j = coef (sum_q P_q h_qj));  Fs[I,set,n]:
  col    : sum_q P_q (h_qj y_j) = g_j y_j       (pointwise, act-coef)
  factor : sum_j g_j y_j = sum_q P_q (sum_j h_qj y_j)   (MH = (P, h), MG = (g))
The ev_a compatibility of the action on cochains is CoefficientEvaluation4's
ev-mulP / ev-A (reused); with the bridge (ev-biT) and (certX), factor shows
that the evaluated kernel generators act by multiples of the ORIGINAL P_q.


5. (4) THE FINITE CORRECTION
----------------------------
ReesCorrection4.Over[K0,A,setA,cfnA,t,a,s,p,e,hp].List[w,fw]:
  for a GenAt list w and fixed bounds fw (§2), the na members of KG,
  dX j = d_j, dU j = n_j, gD j = biT (kg_j) : TPoly D, hgD, hfD, gA j = evT (gD j);
  certs : || Certs ||   (Certs = certificates of the L generators; finite choice)
  Cert[ws]: HX, ht/h/hh (hterm), phi-fac, fac, FA = Factor[na,dX,gA,hgA,h,hh,fac]
  ED = CoefficientEvaluation4.Concrete[K0,A,setA,cfnA,t,a].ED.Input[na,dX,dU,gD,hgD,hfD]
  Seq[c,hc,lift,z,hz,hcompat] with the INPUTS
    c      : Nat -> C^1(-1) over D            (ED.WD.E1)
    hc n   : c_n of coefficient degree n+1
    lift n : || delta c_n = sum_j gD_j u_nj || (CoherentDependence4.Lifted)
    z      : Nat -> C^0(-1) over A
    hz n   : Cong (ev c_n) (delta z_n)        (ev c_n = delta z_n modulo J)
    hcompat n : IJ 1 (z_n - z_0)              (z_n - z_0 in I C^0(M))
  Corr[ws,r] for a weighted result r (CoefficientEvaluation4.evaluated):
    zc = (z_N - sumZ rs) - ev v      (z = z_N - sum_{i<N} ev(r_i) z_i - ev v)
    kernel-terms : sum_j ev(g_j) ev(a'_j) = sum_q P_q (sum_j h_qj ev(a'_j))
    kernel-J     : the explicit J-witness H (ev a') of the kernel-generator terms
    d-zc         : delta z = (delta z_N - sum ev(r_i) delta z_i) - delta (ev v)
    ident        : (ev c_N - sum ev(r_i) ev c_i) - delta (ev v) = sum_j ev(g_j) ev(a'_j)
    cong-d       : delta z = sum_j ev(g_j) ev(a'_j)  modulo J
    closed       : InJ (delta z)        (z closed in the chart complex of M)
    wit-r        : Wit 1 (sum ev(r_i) z_i)   (ev r_i in I^(N-i), N - i >= 1: lower-pos)
    wit-v        : Wit (N+1) (ev v)
    rearrange, reduces : IJ 1 (z - z_0)
  THEOREM correction : || (zz : C^0(-1)) * (InJ (delta zz) * IJ 1 (zz - z_0)) ||
Indexing: c_n (coefficient degree n+1) and z_n are the informal
beta_(n+1) and z_(n+1) of Prop. "finite lifting"; z_0 is the informal z_1.
N = 0 (empty sum) is included.


6. REGRESSIONS (ReesComparisonRegression4) AND MUTATIONS
--------------------------------------------------------
  rect-six, decode11, decode02 : a 2 x 3 rectangle, decoding by computation;
  lower31 (lower-pos) = lower31-comp (computation): 3 - 1 = 2; sub32 : 5 - 3 = 2.
  OverA[A,setA,a1] (t = 1, J = (X_0^3)): y = U_1 X_0^3 (bh : BiHom 1 3),
    g = biT y with hom-g (X-degree 3), coef-g (U-degree 1);
    ev-y : ev_a y = a_1 X_0^3;  ev-g : phi (ev g) = a_1 X_0^3;
    ht : a_1 as a term list of X-degree 3 - 3 = 0 (hterm);  phi-fac, fac;
    factor1 : on C^1(-1): (ev g) y = X_0^3 (a_1 y)  (Factor at this element).
Mutation tests (each restored, tree rechecked):
  zc without "- ev v"                         -> d-zc, rearrange fail;
  witS recursing with Kx instead of Kx + 1     -> witS fails;
  HTerm with HomShift d e (transposed)         -> htermD fails;
  decode11 expecting (1, 2)                    -> decode11 fails.


7. WHAT IS COMPLETED AND WHAT REMAINS
-------------------------------------
COMPLETED (checked, nothing requested assumed):
  (1) the fixed finite list KG (finite index Fin na) with certificates, and
      generation of ker phi by it (finite-generation, finite-list);
  (2) the bridge with both degrees and the evaluation certificates
      (biT, hom-biT, coef-biT, ev-biT, cf-biT, cf-ev, hterm);
  (3) the quotient chart complex (congruence modulo J), images of I^k C(S),
      and the factorisation of the evaluated kernel-generator action
      through the original P_q (Factor.factor);
  (4) the weighted theorem applied to KG, and the finite correction:
      z = z_N - sum ev(r_i) z_i - ev v closed modulo J with z - z_0 in
      I C^0(M) (correction; explicit Corr with witnesses and degrees).
REMAINS (not done here):
  * the finite-fibre section construction producing the INPUTS of Seq:
    the sequence c_n in C^1(-1) over D of coefficient degree n+1 with its
    merely existing lifts along the fixed list KG (delta c_n = sum_j g_j u_nj),
    and cochains z_n with ev c_n = delta z_n modulo J and z_n - z_0 in
    I C^0(M).  Since KG exists only merely, these inputs are stated for a
    given (w, fw); the construction must produce them for that list (or
    for any list), inside the truncation;
  * the final ZMT certificate assembly (from the closed z to the sections
    and the certificate of the theorem).
Limits, stated honestly:
  * The chart module of M is the congruence modulo J C(n) (Cong), not a
    quotient type; delta z in J is MERE (from the merely given hz), while
    the kernel-generator part has the explicit witness kernel-J.
  * hcompat is assumed for every n (only n = N is used).
  * ReesW / presentation are re-instantiated for R over S (§1); the
    identification of the two presentations of A[X_0..X_3] is made once
    per name (GX, var-x0..3, iota-cst, decB, cfnS: <= 0.14 s each).
  * No reverse bridge (term lists over D -> R); not needed.
  * .opens covers 43 of the 460 new declarations.


8. VALIDATION (all commands under timeout 55, from unit/)
--------------------------------------------------------
  ./segc sag/zmt-rees-comparison4 changed / all
      121 modules, 0 failed, OK (all: 3.84 s warm server; new files
      <= 0.41 s each: ReesRings4 0.41, ReesCorrection4 0.22, ReesBridge4 0.13)
  cd sag/zmt-rees-comparison4 ; $(cabal list-bin exe:seg) All.seg
      All.seg: 7653 declarations, 0 failed, 4.3 s, OK
      (7193 = the reused tree of sag/zmt-rees4; 460 new)
  ... All.seg --opened : every new declaration <= 0.14 s
      (ReesRings4.Rings.decB, the identification of the decompositions of
      the tower with those over S); at most 33 definitions opened
      (ReesComparisonRegression4.OverA.ev-y: the tower and the sum over
      Fin 1); in the theorem files at most 30 (ReesCorrection4..Corr.kernel-J:
      the families of MJ, MH and of CoherentDependence4's M0 are the same by
      definition).
  ... All.seg --opens zmt-rees-comparison4.opens
      43 central declarations: "nothing else opened" for each.
  Baseline unchanged, rechecked fresh:
      sag/zmt-rees4/All.seg : 7193 declarations, 0 failed, 3.33 s
  The checking server was stopped afterwards.
