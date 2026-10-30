Local structure of etale algebras (sag/etale-local)
==================================================

Source: ~/COLL/zmt2-revised.tex (T. Coquand, "Local structure of etale
algebras").  This directory formalises Section 4 (the basic examples),
Lemma 1 and Lemma 2.  Informal proofs are at the head of each file.

Check (from unit/):   ./segc sag/etale-local all
Result (30 October 2026): 89 modules, 3985 declarations, 0 failed, 1.3 s.
With ZMT proved and plugged in: sag/etale-local-zmt (README there).

Foundations: the Theory segment of the other sag directories (univalence
and the two parts of replacement as parameters, function extensionality
derived).  No new axioms.  The four files below use only ring laws,
the exterior-algebra determinant library (sag/exterior: Determinant,
Adjugate, ExteriorRelation, Naturality, CharPoly, DeterminantTrick) and
sag/affine (AffineRing, AffinePowers); everything else is a relative link,
unchanged.

Form of the statements.  An algebra given by generators, relations and
inverted elements is described by its points in a commutative ring C (for
an R-algebra C, the images of the coefficients).  An isomorphism of the
note is an equivalence of the point types, natural in C; the algebra
isomorphism follows by Yoneda (sag/fpalg FPYoneda.affine), which is not
re-derived here.


LocalisationExample.seg   (note, Section 4.1)
  Over[C,setC,tau]
    PointE      x with 1 - x tau = 0            (E = R[X]/(1 - X t))
    PointStd    Y = 0 and tau a unit            ((R[Y]/(Y))[1/t])
    equivalence : Equiv PointE PointStd
    zero-fibre  : tau = 0 -> a point of E gives 1 = 0

SimpleRootExample.seg     (note, Section 4.2)
  Over[C,setC,al,be,ga]   (P = aX^2 + bX + c in Horner form x (a x + b) + c)
    y, P, D (= P', D-formula : D = 2 a x + b), s = y D, F, dF (= F'), G = Y F'
    PointEs     points of E[1/s]: P(x) = 0, s(x) a unit
    PointS      points of S = (R[Y]/(F))[1/G]
    equivalence : Equiv PointEs PointS        x |-> a x + b, Y |-> -c/Y
    standard    : F' is a unit on S (S is standard etale)
    Chart1[ai,hai]  a a unit: P = a M (P-M), P' = a M' (D-M), M monic
                (monic); the points of E and of (R[X]/(M))[1/M'] agree
                (root-iff-1/2, unit-iff-1/2)
    cover       : D D = a x D + s;   unit-ideal : 1 = a x/D + s/D^2
    Necessity[hg,bu]  c = 0, b a unit: Y = 0 is a point of
                (R[Y]/(F))[1/F'] (zero-point) but y is never 0 at a point
                of E[1/s] unless 1 = 0 (not-image).  The note's instance is
                R = Z, P = 2X^2 + X.
  Not formalised: the paragraph relating the example to the local
  construction (a prime q with a in q), and the explicit description
  E = Z x Z[1/2] of the Z example.

ResidualIdempotent.seg    (note, Lemma 1)
  Over[k,setk,dec,A,setA,iota,s]   k a discrete field (dec : c = 0 or c a unit)
    value cs    Horner value of a coefficient list at s
    Nonzero cs  some coefficient is a unit; monic-nonzero for monic lists
    strip       first nonzero coefficient: s^m (1 - s v) = 0
    Lemma[cs,nz,root].rel  s^N (1 - s v) = 0 with N = m + 1 >= 1
    Lemma[..].I = Idempotent[A,setA,s,v,m,rel]
  Idempotent[A,setA,s,v,m,rel]   (any commutative ring)
    e = (s v)^N;  idempotent : e e = e
    e-multiple : e = s (s^(N-1) v^N);   e-one : s^N (1 - e) = 0
    Localisation[B,setB,phi]: inverts-s (phi e unit -> phi s unit),
      e-to-one and inverts-e (phi s unit -> phi e = 1): A[1/e] = A[1/s]
  Deviations from the note: the hypothesis is any polynomial relation
  with a unit coefficient (the monic relation coming from finiteness is
  the case monic-nonzero); N = m + 1 always, rather than "multiplying by
  s if necessary".

DeterminantLemma.seg      (note, Lemma 2)
  Map[Rg,Sg,..,phi]   a ring map commutes with delta, finite sums, column
                      replacement and the adjugate (adj-map, from det-nat)
  Over[A,setA,B,setB,iota,y]   (A is the note's R)
    InRy x = Sigma G : A[X]. G(y) = x
    System[n,mu,b,C,eq]  eq : y b_i = C_i(y) + sum_j b_j mu_ji
      p = chi_mu(y) = det(y I - mu)   (det-M)
      system : (y I - mu) b = c;  det-times : det(M) b_k = (adj(M) c)_k
      in-Ry / pb-in-Ry : p b_k = F_k(y),  F_k = sum_i C_i adj(N)_ik
      Generated[coord].px-in-Ry : if the b_j generate B over A, p x is in
        R[y] for every x  (B[1/p] = R[y][1/p])
      Congruence[J,..,J-mu].congruence : p - y^n in J for every ideal J of
        B containing the mu_ji (the note: p = y^r mod m R[y]); by
        ExteriorRelation with  a ~_k c  iff  a - y^k c in J
      Congruence[..].Prime[prime,y-out].p-out : J prime, y not in J ->
        p not in J
  The ideal J is given by its closure properties (0, +, multiplication
  by B); "mu in m" enters only through J-mu.  The note's congruence
  modulo m R[y] is the instance J = m B (or q, which is how it is used).

THE LOOP Q_0, Q_1, ... of Section 1 (remainder version; informal proof and
design in HANDOFF-LOOP.md)

Loop.seg   Over[A,setA,m,m-zero,m-add,m-scale,dec,rad,B,setB,iota,y,W]
  A local, m residually discrete (dec : a in m or a unit; rad : a in m ->
  1 - a unit), B an A-algebra, y in B, W a coefficient list.
  theorem e0 a0 rel0 w0 : Result, for
    rel0 : y^e0 = V_e0 a0                (a monic relation Q_0(y) = 0)
    w0   : InM e0 W(y)                   (W(y) in m R[y], basis form)
  Result = e, a with y^e = V_e a (Q(y) = 0, Q = X^e - [a]_e monic),
           U in A[X], c with Below e c (c_i in m, i < e), and
           W = U Q + [c]_e   in A[X]        (Q-bar divides W-bar in k[X]).
  Files: PowerSums ([c]_e, shift, maps), MonicReduce (Lemma A: Horner
  reduction modulo a monic, generic in an A-algebra), MPart (InM, Lemma B),
  LoopStep (scan for the top unit coefficient, the monic D, all y^j in
  V_d + m R[y]), LoopNakayama (determinant Nakayama: y^j = V_d gamma_j,
  new relation of degree d, transfer of W(y)), Loop (fuel recursion).
  Difference from the note: D_l is the remainder of W modulo Q_l made monic
  at its top unit coefficient, not gcd(Q_l-bar, G^n H-bar); the output
  used in Section 2 is the same.  The hypothesis on W(y) is in basis form
  (coefficients in m on 1, .., y^(e0-1)); a general certificate
  sum mu_j R_j(y) reduces to it by MPart's closure (not packaged).
  Residual openings (0.00 s): Loop.stop0, Step.value, Step.dispatch open
  the polynomial-ring quotient (addQ) when comparing RX.ring.add.

THE Q' STEP (note lines 242-253)

DerivativeStep.seg   Over[A,setA,m,T,setT,iota,eta,J,..,J-m]
  P(eta), P'(eta) = val P, der P: the components of P(eta + epsilon) in the
  dual numbers T[epsilon] (QuadraticPairs with a = 0, linked from
  sag/presentations); val-ev : val P = evaluation at eta.
  UnitMod x = (v) * J (x v - 1)   ("x is a unit in T/J").
  Qprime[G,H,U,Q,n,e,c,b,loop,hQ,hH,hH',hG].result : UnitMod Q'(eta), from
    loop : G^n H = U Q + [c]_e in A[X] (c_i in m), Q(eta), H(eta) in J,
    H'(eta), G(eta) units mod J;  .outside: Q'(eta) in no ideal q
    containing J with 1 not in q.
  Proof: epsilon-component of the loop identity:
    U(eta) Q'(eta) = G(eta)^n H'(eta) mod J.
  Difference from the note: neither H-bar | Q-bar nor the factor D is used
  (the note's own remark at the end of Section 2).  Separability of H-bar
  enters only as "H'(y) is a unit mod m E_g" (hypothesis hH').
LoopQprime.seg   Over[..,W,J,..].Section1[G,H,n,wGH,e0,a0,rel0,w0,hH,hH',hG]
  the loop followed by the Q' step: root (Q(y) = 0), divides
  (G^n H = U Q + [c]_e), q-prime (Q'(y) a unit mod J).
  Residual openings (0.00 s): val-ev, Qprime.epsilon, gn-val and
  Section1.divides/QS open evaluation and quotient internals.

INPUTS OF THE LOOP IN THE NOTE'S FORM

Expansion.seg   Over[A,setA].expand : Bounded d x -> x = sum_(i<d) coef(x,i) X^i
  (with coef-power: the coefficients of X^e are the Kronecker delta).
LoopInputs.seg  Over[A,..,B,setB,iota,y]
  Integral[n',a,bs,eq,c,one].relation : y^n = V_n a0 (n = n'+1) from
    y b_i = sum_j b_j a_ji, 1 = sum c_k b_k (DeterminantTrick.Integral +
    Expansion): Q_0 = chi_a.
  product g h n, product-horner : Horner(g^n h) = Horner(g)^n Horner(h).
  Certificate[e',a0,rel].in-sum : sum_j iota(mu_j) R_j(y) is in InM.
  Section1[J,..,n',a,bs,eq,c,one,g,h,n,k,mu,mu-m,Rs,cert,hH,hH',hG]:
    from generators of B, G and H as lists, the certificate
    (G^n H)(y) = sum_j iota(mu_j) R_j(y), and the special-fibre data
    (H(y) in J, H'(y) and G(y) units mod J):  root (Q(y) = 0) and
    q-prime (Q'(y) a unit mod J); S1.divides is G^n H = U Q + [c]_e.

SECTION 1 IN E_g (item 4: the certificate derived, HANDOFF-ITEM4.md)

IdealGenerated.seg  Lists[B]: append, lmap, lsum f, at (positions),
    lsum-sum (a list sum is FiniteIdeal's Fin-indexed sum).
  Over[A,m,B,iota]: InmB x = x = sum_j iota(mu_j) t_j for a list of
    generators (mu_j in m, t_j in B): the ideal m B, with in-zero, in-add,
    in-scale, in-m (the laws Section1 asks of J).
ClearDenominators.seg  Over[A,..,B,setB,iota,y]
  Full G : every x in B has x G(y)^k = r(y)  (B = R[y][1/G(y)]).
  Clear[G,full].clear : x in m B -> g^K x = sum_j iota(mu_j) R_j(y)
    (one generator at a time; hb-product: (G^e r)(y) = g^e r(y)).
  Clear[..].Certificate[h,hH].cert : the certificate of
    LoopInputs.Section1, (G^n H)(y) = sum_j iota(mu_j) R_j(y), n = K.
  Difference from the note: no extra g^l (the equality is used in E_g,
  not in E), and n may be 0.
Section1Eg.seg  Over[A,..,B,setB,iota,y]
  unit-mod : a unit is a unit mod m B.
  Section1[n',a,bs,eq,c,one,g,h,gu,full,hH,hH']: from the integrality
    equations, G(y) a unit, Full G, H(y) in m B, H'(y) a unit mod m B:
    root (Q(y) = 0), divides (G^n H = U Q + [c]_e), q-prime (Q'(y) a
    unit mod m B).  Hypotheses left: H(y) in m E_g and H'(y) a unit mod
    m E_g (special fibre, E/mE finite etale) and Full (Lemma 2 and ZMT).

SECTION 2: THE ETALE CASE (Stage A of HANDOFF-ETALE-CASE.md)

New links: QuotientRing, RegularIdeal (sag/cffr), TruncationCombinators
(sag/replacement), unchanged.
FormallyEtale.seg   Units[B,setB]: unit-prop, unit-mul/left/right,
    idempotent-one (a unit idempotent is 1), sub-zero, Nilpotent (x v - 1
    = e, e e = 0 gives x a unit);  unit-map.
  Over[A,setA]: SquareZero[B] (ideal, prop, square), Mod[B,N] (B/N,
    projection), reduce (pi h), reduce-at (refl), Lift, Unique,
    FormallyEtale = Lift * Unique, Etale = FormallyEtale * Witness (the
    note's definition: finitely presented + formally etale);
    unit-mod-nilpotent.
StandardEtale.seg   Over[A,setA]
  At[B,setB,iota,a]: value P = P(a), derivative P = P'(a) (dual numbers);
    Taylor[eps,sq].taylor: P(a + eps) = P(a) + P'(a) eps when eps eps = 0.
  Natural: values and derivatives commute with algebra maps.
  deriv P (the polynomial P'), deriv-value: (deriv P)(a) = P'(a).
  Points[Q,G]: g = G Q', IsPoint (Q(a) = 0, g(a) a unit), Point, push
    (h |-> h(s)), Classifies S s (push is an equivalence for every B),
    Standard S = (s : Point S) * Classifies S s  (S is (A[X]/(Q))[1/g(a)]
    up to isomorphism, by its points);  unramified : Unique S.
  Localise[Q,G,F,B,a]: points of (Q, G F) = points of (Q, G) with F(a) a
    unit (to, to-unit, from).
IdempotentIdeal.seg Over[S,setS,K,r,k,gen,a,a-in,eq]: from k_i = sum_j k_j
    a_ji with a_ji in K: f = det(I - a), f-kills-all (f K = 0), one-minus
    (1 - f in K), idempotent (f f = f), generated (x = (1 - f) x on K).
EtaleCase.seg       Over[A,setA]
  Fractions[Q,G,S,s].Full: every x in S is P(s)/g^n (true of the
    construction; an input here).
  Surjection[S,T,u,surj,surj-eq]: Kernel, ideal (I = ker u),
    Factor[B,h,kills].hom (h(I) = 0 gives h = h' u, beta), unique.
  Section2[S,T,u,surj,surj-eq,r,k,k-in,gen]   (generators of ker u: input)
    Square[unramified,lift]: I^2 (truncated certificates), C = S/I^2, N the
      image of I (square-zero), v : T -> C/N, sigma = the lift, equal
      (p = sigma u), in-square (I = I^2), certificates (finite choice).
    Localised[Q,G,st,full,cert]: f, F with f g^n = F(s), t0 = u(s),
      standard : T is standard for (Q, G F).
    Theorem[Q,G,st,full,lift].local : || (F : A[X]) * T standard for
      (Q, G F) ||   (the note's Theorem local in the etale case).
  Inputs left (Stage B): the algebra S standard for (Q, G) with Full (to
  be built, e.g. from presentations/PresentedAlgebra, whose Presentations
  and Algebras are the same files as here); u from Section1Eg (X |-> y,
  Q = S1.Q, G the list g; Q(y) = 0 is root, (G Q')(y) a unit in
  T = E_g[1/Q'(y)], with a bridge DerivativeStep.der = StandardEtale
  derivative); surj (T = R[y][1/g Q'(y)] by Full of ClearDenominators);
  generators of ker u from a presentation of E; Lift T from Lift E.

THE INTRODUCTION (block 2 of HANDOFF-BLOCKS12.md; note lines 75-200)

IdempotentModM.seg  Over[A,m,dec,B,iota,I,..,s]: Lemma 1 read modulo an
    ideal I containing iota(m) (no quotient ring is built): strip (first
    unit coefficient, using dec), Lemma[cs,nz,root].rel: s^N (1 - s v) in
    I; Idempotent: e = (s v)^N, idempotent / e-one / e-multiple modulo I,
    kill (s^K w in I gives e w in I); horner-monic (a monic psum relation,
    LoopInputs.Integral.root, as a Horner value).
HornerValues.seg    Over[A,..,T,setT,kappa,t]: values of coefficient lists:
    horner-add/mul/constant, Map (ring maps), Congruence (t = t' mod K
    gives fs(t) = fs(t') mod K), Shift (sh fs = fs(X + 1), Shifts[A].sh).
Introduction.seg    Over[A,..,E,setE,iota,q,..,q-dec,B,setB,iB,j,j-alg,n',bs,
    coord,s,s-out,zmt]: the hypotheses ZMT (B finite with generators, s not
    in q, s^k z in B), with coord and zmt MERE (Trunc-valued), and, in FieldCase[x0,F0], the field case as
    Factor x0 (root: s^N P(x) in m E; separable: s^N (P'(x) w - 1) in m E;
    generates: s^N (b - C(x)) in m B).
    0. choose: x or x - 1 (P(X + 1)) not in q (Shift).
    The coordinates are chosen in stages (finite choice, EtaleCase.choice),
    each a module parameter:
    Main[x,x-out,F].choice0: coordinates of 1, s, s b_i.
    Main.Step0[c0]: 1. e from Lemma 1 mod m B (Residual[c1,s,cs]); 2. y = x e,
      sys-mod (y b_i = (X C_i)(y) mod m B); choice1: coordinates in m of
      these elements (coords, merely).
    Main.Step0.Step1[cm]: system; 3. Lemma 2 (SYS = DeterminantLemma.System,
      p-out, y-out), g = p s; choice (mere: lists for the F_k, coordinates
      of g b_i and y b_i).
    Main.Step0.Step1.Chosen[ch]: rL (p b as a list value, from coordinates
      of b), G, full (ClearDenominators.FullT G in E: merely), Jsat (J = m E_g read in E: g^k w
      in m E), g-out, q-J (J in q), hG (Lemma 1 mod m B for g), hH (H = P),
      hH' (congruence in the dual numbers), integralE / oneE; clearing
      (ClearDenominators.Clear.clearT: the clearing of denominators,
      merely); Cl[cl]: cert, and S1 = LoopInputs.Section1 in E with J: root-Q (Q(y) = 0),
      Qprime-unit, Qprime-out (Q'(y) not in q).
  Differences from the note: H = P (no gcd with X); Section 1 runs in E
  with J rather than in E_g; the inputs exist merely, since the polynomials
  of Lemma 2 live in the quotient A[X] and lists are chosen for them, and
  since ZMT gives coordinates and s^k z in B only merely.

THEOREM LOCAL (block 1 of HANDOFF-BLOCKS12.md: Stage B of Section 2)

New links (sag/affine, unchanged): AddVariable, ExpressionCongruence,
CongruenceSoundness, PresentedAlgebra, PresentationExistence,
PresentationComparison, EquationExtension, Localization, Generated.
Changed: EtaleCase and IdempotentIdeal take MERE inputs: the section of
u (surj : every t merely has a preimage; Surjection.Factor by unique
values), the generators of ker u (gen), and Full (Fractions.Full is
"every x merely has a Fraction"); Theorem.local eliminates them.
StandardAlgebra.seg  Over[A,setA].Build[Q,G,LQ,Lg,hQ,hg]: S = (A[X]/(Q))[1/g]
    as a presented algebra (PresentationExistence + Localization), point
    s, standard (S is standard for (Q, G)), full (Generated + fractions
    closed under the operations); hornerE / eval-hornerE.
Local.seg  Over[..the Introduction's hypotheses..].Field[x0,F0,etale]:
    theorem : || Conclusion ||, Conclusion = s' not in q, T with
    i : E -> T a localisation at s' (IsLocalisation), and T standard
    for some (Q, G).  Run[c0,cm,ch,cl].Data[lists, expressions, Full at
    the generators of E (fg)]: (a) S; (b)
    T = E[1/g1] (Localization of the presentation of E), u from the
    point y; (c) surj (PreE: z = r(y)/g^k; 1/g1; Generated); (d) kgen
    (f_j(sigma(s)), s - Y(sigma(s))), K, psi : T -> S/K, psi u = pi,
    gen; (e) lift-T from the lifting of E; (f) EtaleCase.Theorem.
    s' = g1 = (G Q')(y) = g Q'(y) (g1-split), not in q (g1-out).
  Hypotheses of Theorem local: the Introduction's (ZMT after the
  refinement, the field case Factor x0, q decidable prime containing
  m E) and etale : FormallyEtale.Etale E (formally etale + a
  presentation).  No new axioms.

TheoremLocal.seg  Over[A,..,E,..,q,..,B,..,coord,s,s-one,zmt,etale]
    .FieldCase[nf,eps,sum-one,xs,pieces].theorem : || Conclusion ||
    (coord, s-one, zmt mere; theorem-of : FieldData -> || Conclusion ||
    packages the FieldCase parameters as one type)
    (Local.Statement.Conclusion).  The hypotheses in the note's form:
    ZMT as in ACL (s in 1 + m E, B[1/s] = E[1/s]) and the field case as
    the decomposition A[1/s-bar] = prod A[1/s-bar] eps_i, eps_i summing
    to 1 in (E/mE)[1/s] (sum-one), each factor k[X]/(P_i) with x_i given
    by its three facts multiplied by eps_i (Piece).  Proof: s not in q;
    find a factor with eps_i not in q (q decidable); refine s' = s eps_i
    (refine: s'^(N+1) w = (s eps^N)(s^N (eps w))); Local.Field.theorem.
    Orthogonality and idempotency of the eps_i are not used.

ZMT (ACL Corollary 1.4) is a hypothesis here and is discharged in
sag/etale-local-zmt (TheoremLocalZMT, with sag/zmt-general).  The
structure of finite etale algebras over a discrete field (TheoremLocal's
FieldCase parameters; E/mE finite for ZMT) remains a hypothesis.

Renamed for the combined tree: LoopStep's inner module Span is PowerSpan
(Span is a file module of sag/zmt-general).
