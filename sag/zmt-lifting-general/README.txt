sag/zmt-lifting-general: general four-coordinate relation certificates
from a supplied finite homogeneous syzygy presentation
=====================================================================

Task: doc/zmt-four-coordinate-handoff.txt, doc/zmt-four-coordinate-command.txt.
Builds on the checked Stages 1 and 2 of sag/zmt-lifting (reused through
relative links, UNCHANGED; see sag/zmt-lifting/README.txt).

STATUS (30 October 2026).  Gates A-D are formalised and checked.
  A  polynomial action on finite Laurent coefficient functions, shifted
     families E0, E1, E2 with A, H and A H = 0, commutation with d;
  B  the top-chart lifting theorem, DERIVED from polynomial syzygy
     generation, and the top coordinates for arbitrary shifts;
  C  raising, constructed zero-reflection, the instance of the Stage 1
     theorem CertifiedDependence, and the dependence export;
  D  the instances g = (P, Q) and g = (P + Q, Q) (P = X_0^3, Q = X_1^3),
     each with its syzygy generation PROVED, not assumed.
This is not full ZMT (see OUT OF SCOPE).

Check:   ./segc sag/zmt-lifting-general all                     (from unit/)
Fresh:   cd sag/zmt-lifting-general && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-lifting-general.opens


1. FOUNDATIONS, ASSUMPTIONS, FILES
----------------------------------
All.seg is the segment Theory of sag/: parameters univ (univalence),
images (replacement) and surjections; fe (FunExt) and propUA derived, as
in sag/zmt-lifting.  Truncation = Truncation.Trunc.  No new axioms: no
choice, excluded middle, SAG/SQC, resizing or noetherian axiom.  The
checker is unchanged.  One universe level l throughout.

The algebraic parameters of the final theorem, and nothing else:
  D : CRing,  setD : isSet D.R,
  cfn : CFN.CFN K0 D                 (only for the dependence step),
  M : HomogeneousMatrices4.Matrices D (the finite homogeneous data),
  ah : Identity M                    (A H = 0, by coefficients),
  syz : SyzGen M                     (polynomial syzygy generation).
Everything else (action, modules, d, A, H, A H = 0 on cochains, the
Laurent lifting, contractions, top coordinates, zero-reflection) is
constructed.

New files (893 declarations):
  PolynomialAction4      polynomials as term lists, the action, its laws
  ShiftedCech4           action on the chart modules, commutation with d,
                         finite products of modules, the polynomial chart
  HomogeneousMatrices4   the data record, Identity, families E0/E1/E2,
                         A, H, A H = 0, differentials of families
  LaurentSyzygyLift4     SyzGen (the supplied hypothesis) and the derived
                         top-chart lifting theorem
  TopCoordinatesShift4   compositions, top lists for any shift, the tagged
                         list, top, pi-zero, pi-expand, recover-T20
  ResolutionCertificate4 Gam, Removable, raising, closure, zero-reflection,
                         the Rel instance
  ResolutionDependence4  the final export
  CubicResolution4       instance 1, recovery of Stage 2
  PolynomialPairExample4 instance 2
  All.seg, README.txt, zmt-lifting-general.opens
Links: every library of sag/zmt-lifting (its own Stage 1/2 files as
../zmt-lifting/X.seg, the others to their real location).  No shared file
was modified; sag/zmt-lifting still checks (section 7).


2. POLYNOMIAL MODEL AND THE SUPPLIED HYPOTHESES
-----------------------------------------------
Exponents of polynomials: N4 = quadruples of naturals (u >= 0 by
construction); size u = ((u0+u1)+u2)+u3.  A polynomial is a term list
  TPoly R = List (R * N4)                         (PolynomialAction4.TPoly)
compared by coefficients: coef p v = sum of the c with (c, v) in p, using
the decidable equality of N4 only (no decision in D).  Products pmul (all
products of terms), finite sums psum (over Fin n), concatenation.

Data (HomogeneousMatrices4.Matrices D), a record with fields
  a b : Nat ;  d : Fin a -> Base.Nat ;  e : Fin b -> Base.Nat ;
  g : Fin a -> TPoly D.R ;  H : Fin a -> Fin b -> TPoly D.R ;
  hg (i)   : HomDeg D.R (d i) (g i)            -- every term: size u = d_i
  hH (i j) : HomShift D.R (d i) (e j) (H i j)  -- every term: d_i + size u = e_j
Zero entries (empty lists) carry no condition: e_j < d_i is allowed.

Hypothesis (i) (HomogeneousMatrices4.Over.Identity):
  Identity M = (j : Fin b) -> CoefZero (psum a (\ i -> pmul (g i) (H i j)))
  i.e. every coefficient of sum_i g_i H_ij is 0.

Hypothesis (ii), HOMOGENEOUS form, quantified over every total degree
(LaurentSyzygyLift4.Over.SyzGen):
  Pol[M,n].F = Fam[M, Sq, setPol, n]: y in Pol[M,n].F.E1 is a vector of
    coefficient functions y_i : Z^4 -> D, finitely supported (merely
    vanishing outside a finite list), vanishing at every exponent with a
    negative coordinate, homogeneous of degree n - d_i;
  Syz y   = (A y = 0)  in Pol[M,n].F.E0, (A y)(m) = sum_i (g_i y_i)(m);
  Lifts y = || (z : Pol[M,n].F.E2.El) * (H z = y) ||;
  SyzGen M = (n : Int) (y) -> Syz y -> Lifts y.
Exported: this homogeneous form.  The polynomial vectors are finitely
supported coefficient functions on N^4 (the explicit model of the handoff
§4); g and H act on them by the term-list action, the only link between
the two representations.  No function choosing z is assumed: the
solutions are given only under truncation.  Negative degrees need no
separate case (a homogeneous polynomial of negative degree is 0).
NOT formalised: the ungraded version of (ii) and the extraction of
homogeneous components from it; the bridge from TPoly to the iterated
PolynomialRing quotient (future work, section 8).


3. ACTION AND SHIFTED COCHAINS (Gate A)
---------------------------------------
PolynomialAction4.Over[D,setD]:
  mulP p f m = sum_{(c,u) in p} c f(m - u)        (finite, no decision on D)
  mulP-cong, -zero, -add, -neg, -sm, -sub, the shapes -T, -Q of d;
  mulP-app (lists add), mulP-pmul (products compose), mulP-psum,
  mulP-shift (commutes with any exponent map commuting with m - u;
              in particular X^L and X^-L);
  act-zero  : CoefZero p -> mulP p f m = 0;
  act-coef  : equal coefficients -> equal action (invariance).
  Proof of act-zero (expand): (p f)(m) = sum_{v in L} coef p v f(m - v)
  over L = nub (exponents of p), deduplicated by the decidable equality of
  N4 (Nub.nub-nodup, nub-mem); each exponent occurs once (lsum-single).
  No polynomial is reconstructed from a support list with repetitions.
ShiftedCech4.Over[D,setD]:
  Act[I,set,k,k',p,hp].lin : C(k) -> C(k') for every chart type (I, set)
  when k' - size u = k for each term (Shifts): chart and degree conditions
  (van-mulP, out-subE, not-deg-subE), finite support (vanish-mulP: the
  list S + u), linearity.  Comm.d0/d1/d2: d commutes with every p.
  Only d is commuted with polynomials; the contractions never are.
  Prod (finite products), SumMap, Into, Each, LinSum.lin-sum, ChartSums.
HomogeneousMatrices4.Over[D,setD]:
  Fam[M,I,set,n]: E0 = C(n), E1 = prod_i C(n - d_i), E2 = prod_j C(n - e_j),
    gi i : C(n - d_i) -> C(n), hij i j : C(n - e_j) -> C(n - d_i)
    (hg-shifts, hH-shifts), A = SumMap gi, H = Into (SumMap hij);
    AH (ah) z : A (H z) = 0   (lin-sum, sum-swap, mulP-pmul, mulP-psum,
                               act-zero on the Identity: Col.zero).
  DiffFam[M,I,setI,J,setJ,Dq,comm,n]: d0, d1, d2 (componentwise),
    dA : d (A y) = A (d y),  dH : d (H z) = H (d z).
  Cochains: n = -1 (TopList4.mOne), (I,set) = (Pt,setPt) .. (Sq,setSq);
  E0^q = C^q(-1) is literally Cech4.Over.Deg[mOne].Cq.
  The contractions of Stage 2 (Cech4Contraction.Contr[k], every k) are
  reused, applied componentwise at the twists -1 - d_i, -1 - e_j.


4. THE LOCALISATION BRIDGE AND TOP COORDINATES (Gate B)
-------------------------------------------------------
THEOREM (LaurentSyzygyLift4.Over.Lift[M,syz].lift), CONSTRUCTED from syz:
  (y : F.E1.El) -> Id F.E0.El (F.A.f y) 0 -> || (w : F.E2.El) * Id (F.H.f w) y ||
  with F = Fam[M,Sq,setSq,-1]: y in E1^3 = prod_i C^3(-1-d_i) (fully
  inverted chart), w in E2^3 = prod_j C^3(-1-e_j).
Proof (file comment):
  * the support witnesses of the y_i (finitely many truncations) are
    eliminated at once into the truncated goal (fin-choice, induction on
    the rank);
  * one common monomial X^L: L = coordinatewise sum of the negative parts
    of all exponents of the support lists (bound); s + L >= 0 for s in the
    lists (bound-le, fits);
  * y' = X^L y (Xmul): a polynomial vector of degree n' = -1 + size L,
    with finite support S + L; A y' = X^L (A y) = 0 (mulP-shift);
  * syz at n' merely gives z with H z = y' (z_j of degree n' - e_j);
  * w = X^-L z (Xinv, in C^3(-1-e_j)), H w = X^-L (H z) = y.
  All support, degree and equality witnesses are constructed.

Top coordinates (TopCoordinatesShift4):
  comps k N: the k-tuples of naturals with sum N; nodup-comps, complete
  (generic proofs by induction on k and N).  topList e: the quadruples with
  sum e - 3 (all-negative exponents topE n = (-1-n_i) of degree -e-1;
  empty for e < 3).  TopMem.mem: every all-negative exponent of degree
  -e-1 is topE of a member.  recover-T20: for e = 6 the list is literally
  TopList4.T20 (refl).  tagged b e: the pairs (j, n), n in topList(e_j),
  over j < b; m = len (tagged b e) is arbitrary (b = 0, empty lists allowed;
  no positivity assumed).
  Over.Top[M].top : E2^3 -> D^m, top(w)_k = w_j(topE n) for the k-th entry.
  THEOREM pi-zero : top(w) = 0 -> piE(w_j) = 0 for every j.
  Reconstruction pi-expand : pi(w_j) = sum_{n in topList(e_j)} w_j(topE n) X^(topE n),
  and coord-at: these coefficients are the coordinates of top(w).


5. CERTIFICATE AND DEPENDENCE (Gate C)
--------------------------------------
ResolutionCertificate4.Over[D,setD].Cert[M,ah,syz]:
  Z = F1.E0 = C^1(-1),  V = TP.V = D^(len TL).
  Witness c p = (u : E1^2) * (w : E2^3) * (d c = A u) * (d u = H w) * (top w = p)
  Gam c p = || Witness c p ||
  Bdry c = (h : E0^0) * (a : E1^1) * (c = d h + A a);  Removable c = || Bdry c ||
  Raise[c,u,e1]: syz' (A (d u) = d (A u) = d d c = 0), partner (via
    Lift.lift, under the one truncation); partner c : || Lifted c || -> || Partner c ||.
  gam-zero, gam-add, gam-sm: componentwise closure.
  Reflect[c,x] (CONSTRUCTED; not a hypothesis): t_j = sigma(w_j), d t = w
    (pi-zero, sigma-eq); u' = u - H t, d u' = 0 (dH); a_i = con2(u'_i),
    d a = u'; c' = c - A a, d c' = A (u - u') = A (H t) = 0 (dA, AH);
    h = con1(c'), c = d h + A a.  Exported: Reflect.bdry : Bdry c (the
    primitive), then reflect : Gam c 0 -> Removable c.
  rel : RelationCertificate.Rel[D, Z, V].

FINAL THEOREM (ResolutionDependence4.Over[K0,D,setD,cfn].Dep[M,ah,syz].Seq[c,lift].dependence):
  c    : Nat -> C^1(-1),
  lift : (n : Nat) -> || (u : E1^2) * Id (d c_n) (A u) ||
  ----------------------------------------------------------------
  || (qs : List D.R) * Bdry (c_(len qs) - sumL qs) ||,
  i.e. merely N = len qs (N = 0 allowed), q_0..q_(N-1), h in E0^0,
  a in E1^1 with c_N - sum_{i<N} q_i c_i = d h + A a.
  Proof: CertifiedDependence.Over (Stage 1, unchanged) for Cert.rel with
  partners \ n -> Cert.partner (c n) (lift n): each raising is applied
  under its own truncation; no Nat-indexed u_n or w_n is chosen; the
  primitive's truncation is flattened (bind).


6. REGRESSION INSTANCES (Gate D)
--------------------------------
CubicResolution4.Over[D,setD] (any commutative set-ring D):
  M1: g = (P, Q), H = (-Q, P)^T, d = (3,3), e = (6); degrees by refl.
  id1 : Identity M1 (P(-Q) + QP has coefficients 1 + (-1 + 0) or 0, cancel).
  syz1 : SyzGen M1, PROVED over any D (Syz1): from P y_0 + Q y_1 = 0,
    z(m) = y_1(m + 3e_0) is a polynomial (P divides y_1: Off.first uses the
    relation at m + 3e_0 + 3e_1), -Q z = y_0, P z = y_1 (shift injectivity).
  R = Cert[M1,id1,syz1].
  lift-conv : a Stage 2 lift (d b = P u + Q v) gives the general one;
  bdry-conv : a general primitive gives the Stage 2 form (d h + P a0) + Q a1;
  Dependence[K0,cfn].Seq[b,lift].stage2 : the conclusion of the general
    theorem in LITERALLY the type of CubicDependence.Over.Seq.Result
    (the two finite sums are identified by sumL-eq);
  nonzero example: gamN : R.Gam bE (top wN) for CubicExample's bE, w;
    coordN : the coordinate of top wN at the head (j_0,(0,0,0,3)) is 1;
    nonzeroN : 1 /= 0 -> top wN /= 0; OverZ.nonzero-Z over Z;
    m20 : len R.TP.TL = 20 (refl).  OverZ.DZ: the dependence over Z.
PolynomialPairExample4.Over[D,setD]:
  M2: g = (P + Q, Q), H = (-Q, P + Q)^T (P + Q a two-term list, used in
    both A and H; the general theorem is used unchanged).
  id2 : Identity M2 (coefficients a + (b + (-a + (-b + 0))) = 0).
  syz2 : SyzGen M2, DERIVED from syz1 by (P+Q) y_0 + Q y_1 = P y_0 + Q (y_0 + y_1):
    instance 1 applied to (y_0, y_0 + y_1) gives z, and (H z)_1 = P z + Q z
    = (y_0 + y_1) - y_0 = y_1 (fin2).
  R2 = Cert[M2,id2,syz2];  Dependence2[K0,cfn].dependence;  OverZ.DZ.
  act-check : (P + Q) w has coefficient 1 at the exponent of P w
    (a concrete coefficient equality, by computation of the decisions).


7. VALIDATION
-------------
  timeout 55 ./segc sag/zmt-lifting-general all
      77 modules, 0 failed, OK (0.01-0.7 s, warm server)
  cd sag/zmt-lifting-general ; timeout 55 $(cabal list-bin exe:seg) All.seg
      All.seg: 4231 declarations, 0 failed, 1.26-1.27 s, OK
      (3338 of them are the unchanged sag/zmt-lifting tree; 893 are new)
  ... All.seg --opened                         (max 0.01 s per declaration)
  ... All.seg --opens zmt-lifting-general.opens
      90 declarations: "nothing else opened" for each.
  Old development, rechecked:
      ./segc sag/zmt-lifting all : 68 modules, 0 failed, OK
      fresh sag/zmt-lifting/All.seg : 3338 declarations, 0 failed, 0.88 s
  Mutation test: replacing -Q by Q in H (instance 1) makes id1,
  Syz1.pt0, ptu and, in instance 2, Id2.zero and Syz2.FromM1.pt1 fail;
  restored.

  New declarations per file (max definitions opened by one declaration):
    PolynomialAction4      125     7
    ShiftedCech4            85    16
    HomogeneousMatrices4    75    26
    LaurentSyzygyLift4     106    58
    TopCoordinatesShift4   155    25
    ResolutionCertificate4 122    18
    ResolutionDependence4   22     7
    CubicResolution4       128    63
    PolynomialPairExample4  75    51
  (Stage 2's maximum was 1957.)  The .opens lists were compared with the
  informal proofs: they name the notions each proof is about (mulP, pmul,
  coef, comps, Shifts, ...) and the carriers of the modules it works in
  (Chart.mod/El/val, SubMod.mod/E, Prod.mod/El, Fam.C1/C2, regular, TPoly).
  Those carrier openings are representation costs, not hidden steps.  The
  largest counts are in the instances, where the twists -1 - 3 = -4 and
  -1 - 6 = -7 of the general modules are identified with Stage 2's mFour,
  mSeven by computation on closed integers (sucZ, sucNeg, three, ..), and
  in coordN/act-check, which compute decisions on concrete exponents.


8. REMAINING OBLIGATIONS AND SCOPE
----------------------------------
Within this milestone: none of the requested constructions is assumed.
Limits, stated honestly:
  * (ii) is exported in the homogeneous form (section 2); the ungraded
    form and the homogeneous component extraction are not formalised;
  * the polynomial model is term lists with equality by coefficients
    (for g, H, the Identity) and finitely supported coefficient functions
    (for the vectors in (ii)); no bridge to the iterated PolynomialRing
    quotient of sag/polynomial is formalised (future work);
  * finite support is "vanishes outside a finite list" (repetitions
    allowed), as in Stage 2;
  * the .opens specification covers 90 central declarations, not all 893.
OUT OF SCOPE (not proved here): full ZMT; arbitrary dimension (only four
coordinates); construction of partial homogeneous resolutions or of
syzygies by CFN coherence (syzygy generation is an input, proved only for
the two instances); weighted/bigraded polynomial dependence; the Rees
presentation/comparison; finite-fibre sections and arbitrary-base
assembly; generation of the cohomology or of the finite top kernel.
