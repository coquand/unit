sag/zmt4: the four-coordinate ZMT certificate (ZMT4) -- IN PROGRESS
==================================================================

Task (30 October 2026): complete ZMT4 from sag/zmt-rees-comparison4 --
construct the finite-fibre inputs of ReesCorrection4, apply the correction,
extract the integral certificate, export it to sag/zmt-descent.

STATUS (30 October 2026).  NOT COMPLETE.  This directory does NOT prove
UniversalZMT 3 or CFNZMT 3.  Checked: the certificate end (ZMT4Certificate),
the residual-equation setup and homogenisation (ZMT4Setup), the tools for
chart cochains as term lists (ZMT4Polynomials), the EXTRACTION
(ZMT4Extract.Sec.extract: a section closed modulo J and congruent to Z^-1
modulo I gives a ZMT certificate for the residual algebra), and a
CONDITIONAL assembly (ZMT4Assembly: the inputs of ReesCorrection4 with
z_0 = Z^-1 on the chart Z give a certificate).  Remaining: (D) the
finite-fibre sections and (E) the Rees lifts with their lifts along KG,
then (F) the export; stated exactly in §3.  They are parameters only of the
module ZMT4Assembly.Inputs, which is labelled conditional and is not
claimed to prove ZMT.  Not committed to git.

Check:   ./segc sag/zmt4 all                     (from unit/)
Fresh:   cd sag/zmt4 && $(cabal list-bin exe:seg) All.seg
Links: the link set of sag/zmt-rees-comparison4 (its six files as
../zmt-rees-comparison4/X.seg) united with that of sag/zmt-descent (its own
files as ../zmt-descent/X.seg); every shared name has the same target
(checked).  No shared or earlier file was modified; no checker change, no
new axiom, no new Theory parameter.


1. THE ARGUMENT, BACKWARDS FROM THE CERTIFICATE
-----------------------------------------------
Target (zmt-descent): UniversalZMT 3, i.e. for residual data D0 over the
CFN ring A = Z[C_1..C_m] with three variables, a ZMTCert for the residual
algebra E = F(D0) = A[X_1,X_2,X_3]/(f_i), f_i = P_i(X_i) - sum_j b_j H_ij(X),
P_i monic, I = (b_1..b_t).  (CFNDescent.universal-of-cfn is not needed: the
residual algebras are exactly what the descent uses.)  Fewer than three
variables would be handled by padding (P = T for an extra variable); four
homogeneous coordinates support exactly three affine generators -- no claim
for arbitrary dimension.

(a) Certificate from degree-lowering relations (ZMT4Certificate, DONE).
    s = deh sT (sT homogeneous of degree D), s = 1 + sum_j b_j v_j and
        s y_k^(m_k+1) = deh q_k,  q_k homogeneous of degree m_k   (DL)
    give monic equations for s, s y_1, s y_2, s y_3: V = F_d E,
    d = D + m_1 + m_2 + m_3, is spanned by the box family y^a (a_1+a_2+a_3 <= d)
    and stable under s and every s y_k (Red: either some beta_k > m_k and
    (DL) lowers the degree, or the total y-degree is <= m_1+m_2+m_3 and the
    representative sT of s is used); DeterminantTrick.Integral and
    CharacteristicMonic.CharMonic give the Monic data.
(b) (DL) from a section closed modulo J (ZMT4Extract, DONE).
    J = (P_q), P_q the homogenisations of the f_q (ZMT4Setup, DONE: deh P_q = 0).
    If z in C^0(-1) (A-chart cochains on the four charts, p0 = the chart
    Z = X_0) has delta z in J C^1(-1) and z - z_0 in I C^0(-1) + J C^0(-1),
    with z_0 = Z^(-1) on the chart p0, then multiplying the identity on the
    edge {Z, X_k} by Z^a X_k^b (a, b bounding the finitely many negative
    exponents) and dehomogenising gives s y_k^b = deh(X_k^b z_k), of degree
    b - 1, with s = deh(Z^a z_Z); on the chart p0 the same gives
    s = 1 + sum_j b_j deh(Z^a x_j).
(c) The closed section: ReesCorrection4.correction (DONE in
    sag/zmt-rees-comparison4) from the inputs of (d), (e).
(d) Finite-fibre sections z_n (§3 (D)).
(e) Rees lifts c_n and their lifts along the kernel list KG (§3 (E)).


2. CHECKED FILES
----------------
ZMT4Certificate (138 declarations).  Over[R,setR,E,setE,iota,y] (any
commutative ring map, y : Fin 3 -> E):
  deh p = sum iota(c) y^u (Z ignored); mon-add, deh-scale, hom-scaleT;
  V[d]: box generators g (WeightedParts4.rangeN / decode), expand
    (deh w = sum_j g_j iota(cf_j w) for w of degree d, by range-single in
    each coordinate), one (1 in V), Integral[z,act] (Cayley-Hamilton);
  Data[s,D,sT,hsT,esT,m,q,hq,dl,t,b,cong]:
    Red[c,b1,b2,b3,h].res : s y^beta = deh w, w of degree d, for
      size beta = d + 1 (big1..big3, small; decisions only on naturals);
    THEOREM certificate : ZMTCert[R,E,iota,3,y,t,b].
ZMT4Setup (58 declarations).  Over[A,setA,D0] (D0 : Residual[A,setA,3]):
  E = F(D0), deh-app, deh-pmul; tl : Expr -> TPoly, deh-tl : deh (tl e) = e(y);
  fT q = tl f_q, deh-f : deh (fT q) = 0; homT, hom-homT, deh-homT (under the
  degree bound bndT, bnd-le);
  P q = homT e_q (fT q), hp : HomDeg e_q (P q), deh-P : deh (P q) = 0.


3. REMAINING OBLIGATIONS (exact statements; not assumed anywhere)
-----------------------------------------------------------------
Notation: ST = ZMT4Setup.Over[A,setA,D0]; CH = ReesChart4.Over[A,setA,D0.t,
D0.b,3,ST.P,ST.e,ST.hp]; CJ0 = CH.JC[Pt,setPt,mOne], CJ1 = CH.JC[Ed,setEd,mOne];
d = (Cech4.Over[A,setA].D0 mOne).f.

(C) Extraction -- DONE (ZMT4Extract.Over[A,setA,D0].Sec[z,z0,hz0].extract).
    For z, z0 : CJ0.E.El with
      (CJ0.E.val z0 p0 m) = [m = (-1,0,0,0)]   (z_0 = Z^-1 on the chart Z),
      CJ1.InJ (d z),  CJ0.IJ 1 (z - z0)
    merely the Data of ZMT4Certificate for (E, iota, y): hence
    || ZMTCert[A,E,iota,3,y,D0.t,D0.b] ||.
    Proof as in §1 (b): ZMT4Polynomials (decOut, filt, Lpat, dom-pat,
    ChartPoly, filtT, cf-filt, Deh.deh-cf) and ZMT4Extract (HP, Edge for
    the edges {Z, X_k}: cf-J, cf-id, dl; the chart Z: cf-Z, cong; Data).
    The finitely many truncated supports (of z, of the J-witnesses on the
    three edges and on the chart Z, of the t members of the I-witness) are
    combined by LaurentSyzygyLift4.fin-choice (W.cert).

(D) Finite-fibre sections.  For every n (merely, per n -- no sequence of
    choices): z_n : CJ0.E.El with
      z_n = Z^-1 on the chart Z;
      d z_n = w_n + sum_q P_q y_q,  w_n in I^(n+1) C^1(-1) with an
        explicit witness (FiniteIdealPowers.Wit (n+1));
      z_n - z_0 in I C^0(-1) + J C^0(-1).
    Construction (doc/zmt-formal-cohomology.tex, "Finite-fibre sections in
    an algebraic chart model", specialised to residual algebras): on the
    chart X_k, u = Z/X_k, the homogenised equation gives
    G_k(u) = u^delta H_k(u) = sum_j b_j h_kj  modulo J, H_k(0) = 1, so
    H_k^(n+1) = 1 + u Q_n; with L >= every delta (n+1),
      1 = a(u) H_k^(n+1) + b(u) u^L,  a = sum_{i<L} (-u Q_n)^i,  b = (-Q_n)^L
    (explicit), e_k = b(u) u^L, t_k = -e_k Q_n, z_n = t_k / X_k on the chart
    X_k and Z^-1 on the chart Z.  Overlap identities modulo
    I^(n+1) C + J C: on {Z, X_k}, z_k - Z^-1 = -(a + e_k) u^-L ... G^(n+1)/Z;
    on {X_k, X_l}, e_k (1 - e_l) and e_l (1 - e_k) are in I^(n+1) + J (u_k^L
    = u_l^L (X_l/X_k)^L), hence e_k = e_l, and z_k - z_l = e_k (z_k - z_l)
    = b_k u_k^(L-1) (Z (z_k - z_l)) / X_k with Z (z_k - z_l) = e_k - e_l
    modulo I^(n+1) + J.  All products are of a homogeneous polynomial in
    (Z, X_k) with a Laurent shift X^(-N), i.e. term-list actions (mulP) and
    shifts (mulP-shift); the congruences are polynomial identities in S
    with I^(n+1)-witness trees.  No properness or separatedness argument is
    used.  Estimated 600-1000 declarations; no mathematical obstruction
    identified.

(E) Rees lifts.  From the explicit witness w_n of (D), c_n = the Rees lift
    of w_n (a D-cochain, D = A[U], of coefficient degree n+1 with
    ev c_n = w_n: replace each b_j of the witness tree by U_j), so
    ev c_n = d z_n modulo J (hz) holds by construction.  The lift
      lift n : || d c_n = sum_j gD_j u_nj ||   (CoherentDependence4.Lifted)
    along the fixed list KG of ReesCorrection4.List[w,fw] needs the
    LOCALISED KERNEL MEMBERSHIP: a D-cochain x homogeneous of U-degree
    n+1 with ev x = sum_q P_q y_q (here x = d c_n, ev x = -sum_q P_q d y_q)
    is merely sum_j gD_j u_j.  Proof plan: clear denominators (X^L per
    component, as in (C)); the term list xi of X^L x over D lies in
    ker(D[X] -> M[T]); transfer to R = S[U] needs a ring map
    Psi : R -> D[X] (S[U] -> A[U][X], the exchange of the two variable
    orders, by the universal properties of the towers) with
    Psi o biT-compatibility and a preimage of every term list
    (ReesBridge4 builds only the direction R -> term lists over D, for
    bihomogeneous elements); then ReesFiniteList4.kernel gives the
    combination of KG, ReesBridge4.biT brings it back, homogeneous parts
    and X^(-L) (mulP-shift) give the u_j.  Estimated 400-600 declarations;
    the representation work (two towers) is the main cost; no mathematical
    obstruction identified.  Note: the KG relations are required --
    J and the Koszul relations do not suffice without flatness (the
    elimination ideal of zmt-rees4).

(F) Export.  ZMT4Assembly.Over[K0,A,setA,cfnA,D0].Inputs[w,fw,c,hc,lift,
    z,hz,hcompat,hz0].certificate composes the correction with the
    extraction (checked; conditional on its parameters).  With (D), (E): for residual data D0 over Z[C_1..C_m] (n = 3),
    ReesRings4.WithCFN.finite-list gives merely (w, fw); inside that
    truncation, for every n, (D) and (E) give the inputs of
    ReesCorrection4.List[w,fw].Seq; correction gives merely z; (C) gives the
    certificate.  The sequences c, z of Seq are functions of n built by
    explicit formulas from (D) (z_n explicit; only the lift of d c_n along
    KG is truncated, per n, which is the form of Seq's hypothesis).  This
    yields UniversalZMT 3 and, with zmt-descent, the arbitrary-base
    theorem for three generators; padding gives n = 1, 2.  Not started.


4. FILES AND VALIDATION
-----------------------
New files (542 declarations, no body-less declaration):
  ZMT4Certificate   (a) the certificate from (DL)                         138
  ZMT4Setup         residual equations, homogenisation, deh               58
  ZMT4Polynomials   chart cochains as term lists, deh through coefficients 92
  ZMT4Extract       (C) the extraction theorem                           196
  ZMT4Assembly      the conditional composition with ReesCorrection4      32
  ZMT4Regression    regressions                                           26
  All.seg, README.txt, zmt4.opens
Regressions (ZMT4Regression): at the point y = 0 of any ring (E = A, I = 0)
  the degree-lowering data s = 1, q_k = [] give a certificate through the
  whole determinant-trick construction (Point.certificate), and the stable
  module has one generator, so the monic equations have degree 1
  (deg-one, by computation); Setup: hp and deh-P for any residual data.
Mutation tests (each restored, tree rechecked): the small reduction with
  the Z-exponent k1 + k2 (k3 dropped) -> Red.small fails; q_k of degree
  b_k + 1 -> Edge.HK, hqF fail; homogenisation with one Z too many ->
  hom-term, deh-term-hom fail; deg-one expecting 2 -> deg-one fails; s
  taken from z_0 instead of z -> HS, Edge.cf-id, cf-Z fail.
Commands (all under timeout 55, from unit/):
  ./segc sag/zmt4 changed / all : 0 failed
  cd sag/zmt4 ; $(cabal list-bin exe:seg) All.seg
      All.seg: 10500 declarations, 0 failed, 5.4 s, OK
  ... All.seg --opened : every new declaration <= 0.04 s
      (ZMT4Extract..L.cf-Z); at most 38 definitions opened (..L.hY: the
      pointwise reading of a J-witness on the chart Z).
  ... All.seg --opens zmt4.opens : 35 central declarations, "nothing else
      opened" for each.
  Baselines unchanged, rechecked fresh: sag/zmt-descent 5424 declarations,
  0 failed; sag/zmt-rees-comparison4 OK.
  The checking server was stopped afterwards.

5. WHAT REMAINS, IN ORDER
-------------------------
(D) the finite-fibre sections (explicit, per n), (E) the Rees lifts and the
localised kernel membership along KG (the exchange of the variable orders
S[U] <-> A[U][X] is the main representation work), (F) instantiating
ZMT4Assembly.Inputs inside the truncation of ReesRings4...finite-list to
obtain UniversalZMT 3, and padding for one and two variables.  No
mathematical obstruction has been identified; the estimates of §3 are the
honest size of the work.
