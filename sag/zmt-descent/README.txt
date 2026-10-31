sag/zmt-descent: arbitrary-base descent of ZMT certificates from an
explicit CFN-base certificate principle
=====================================================================

Task: doc/zmt-arbitrary-base-handoff.txt, doc/zmt-arbitrary-base-command.txt
(proof: doc/zmt-formal-cohomology.tex, "Reduction to an arbitrary base
ring", simplified as in the handoff: only the residual monic equations are
imposed, over a polynomial ring over Z).

STATUS (30 October 2026).  Gates A-D and the regression instances are
formalised and checked.  The universal coefficient base Z[C_1..C_m], its
CFN structure, the lifted residual data, the universal residual algebra F0,
the compatible map F0 -> E, the finiteness of the special fibre of F0 and
the extraction of residual data from a finite fibre are all CONSTRUCTED.
The one unproved input is the CFN-base ZMT certificate principle, which is
an explicit module parameter (U0 : UniversalZMT n, or Z : CFNZMT n) of the
final theorems -- never an axiom, never a field of a record whose other
fields contain the descent.  This development does NOT prove ZMT.
Second milestone (same day, QuotientFibre): the bridge from the usual
hypothesis "E/IE is finite over R/I" (quotient rings R/I, E/IE, the induced
structure map) to the elementwise FiniteFibre, and the certificate theorem
with the usual hypothesis.
Third milestone (CertificateSubalgebra, CertificateLocalisation): from a
certificate, B = R[s, s x_1, .., s x_n] is constructed, B is finite over
R, and B[1/s] -> E[1/s] is constructed and proved an isomorphism (the
optional consequence of handoff §7).
Fourth step (FiniteFibreLocalisation): the usual-form ZMT conclusion from
the usual hypotheses, conditional on the principle.

Check (from unit/):
  timeout 55 ./segc sag/zmt-descent all
Fresh:
  cd sag/zmt-descent && timeout 55 $(cd ../.. && cabal list-bin exe:seg) All.seg
Audit:
  ... All.seg --opened ;  ... All.seg --opens zmt-descent.opens

Results (30 October 2026, checker unchanged; after the third milestone):
  fresh   All.seg: 5424 declarations, 0 failed, 1.66 s, OK
  segc    117 modules, 0 failed, 1.31 s, OK
  (FiniteFibreLocalisation: 54 declarations, all 0.00 s)
  new files: 1210 declarations (858 + QuotientFibre 79 + QuotientExamples
          51 + CertificateSubalgebra 94 + CertificateLocalisation 100 +
          LocalisationExamples 28; RegularIdeal, QuotientRing and the four
          localisation files are links);
          every module <= 0.04 s, every declaration
          <= 0.01 s; at most 35 distinct definitions opened by a declaration
          (the regression T5.y-is; in the main files Fibre.all-mul, 30, all
          aliases of the presented algebra);
  --opens zmt-descent.opens: 129 central declarations (58 + 25 of the
          quotient bridge + 38 of B and the localisation + 8 of the final
          theorem), 129 "nothing else opened".


1. FOUNDATIONS AND ASSUMPTIONS
------------------------------
All.seg is the segment Theory of sag/ (as in sag/zmt-weighted4): parameters
univ (univalence), images (replacement) and surjections; fe and propUA are
derived.  Truncation = Truncation.Trunc.
  * No new axioms, no new Theory parameter, no choice principle: finite
    choice is FinCat.fchoice (proved by induction on Fin n).  No excluded
    middle, no SAG/SQC, no resizing.
  * Nothing is assumed of the arbitrary base R: no CFN, discreteness,
    domain, field, characteristic or nontriviality hypothesis; no equality
    in R is ever decided.  The coefficient map h : Z[C] -> R and the map
    phi : F0 -> E are neither injective nor surjective in general.
  * The ideal I of R in Gate D is ANY predicate I : R -> U; IE is the set of
    finite sums sum_k iota(a_k) w_k with a_k in I (IdealWitnesses).  No
    closure property and no finite generation of I is used.
  * The CFN principle is a module parameter (section 3).
  * No body-less declaration in the new files other than record fields;
    the records (Monic, ZMTCert, Residual, IEWit, VecWit, FiniteFibre,
    Certified) are always instantiated by constructions or hypotheses.
  * No shared or earlier file was modified.  Dependencies are relative
    symlinks (122), the link set of sag/zmt-weighted4 plus
    presentations/{ExpressionCongruence,CongruenceSoundness,PresentedAlgebra,
    PresentationExistence,Equivalences} and exterior/{TorsorCocycles,
    AffineHLevels,MnAlgebra,AlgSIPUA,AlgSIPInd,AlgSIPTransport,Alternating,
    ExteriorUniversal,ExteriorContr,ExteriorContrUA,ExteriorDegree,
    Determinant,Adjugate,ExteriorRelation,Naturality,CharPoly,
    DeterminantTrick} and cffr/{RegularIdeal,QuotientRing} (the existing
    quotient ring R/I of an IdealPred with propositional membership), and
    the existing localisation at the powers of one element:
    horrocks/{LocalizationIdentities,MonoidFractions,MonoidLocalization},
    jacobian/PowerLocalization.
  * The ideal laws of I (RegularIdeal.IdealPred: zero, sums, multiples;
    membership a proposition) are assumed ONLY in QuotientFibre;
    FiniteFibreCertificates is unchanged and still takes any predicate.


2. REPRESENTATIONS
------------------
Monic polynomials (ZMTCertificate.Monic A): a degree d and lower
coefficients low : Fin d -> A,  P(T) = T^d + sum_k low_k T^k.  The index k
of Fin d is the exponent k (Fin (d+1) = Fin d + 1, its new element inr tt
is the exponent d).  The leading coefficient is the literal 1, so
monicity is part of the data and is preserved by mapM h (map the lower
coefficients, same degree).
  Eval[A,F,iota].mev P z = z^d + sum_k pw z d k * iota(low_k)   (pw = 1,z,..)
The bridge to the polynomial ring A[X] = PolynomialRing.Extension is
CharacteristicMonic.Expansion: for p with degree bound B,
ev_z(p) = sum_(j<B) iota(p_j) z^j (expand), and the characteristic
polynomial chi (bound N+1, coefficient 1 at N) evaluates as the Monic of
its lower coefficients (CharMonic.ev-chi).

Polynomials in X_1..X_n: expressions Presentations.Over[A,setA].Expr (Fin n)
(variables, constants, sums, products) with their evaluation in any
A-algebra; every element of A[X_1..X_n] is the value of one.  Algebra
generation of E by x is: every e is merely the value at x of an expression.

Congruences modulo a finitely generated ideal: FiniteIdeal.Over[F,t,B]
.Certificate x y = (v : Fin t -> F) * (x = y + sum_j B_j v_j).


3. EXACT SIGNATURES
-------------------
(Within the segment Theory, at level l.  Fin = Presentations.Fin.)

Certificate (ZMTCertificate.ZMTCert[A,F,iota,n,y,t,b]):
  s : F ;  cong : FiniteIdeal.Over[F,t,\ j -> iota(b_j)].Certificate s 1
  (i.e. s = 1 + sum_j iota(b_j) v_j) ;  q0 : Monic A ;  ann0 : q0(s) = 0 ;
  q : Fin n -> Monic A ;  ann i : (q i)(s y_i) = 0.

Gate A (CertificateTransport.Over[A,R,h,F,E,iF,iE,phi,compat,n,y,x,hy,t,b,a,hb]):
  compat : (a) -> phi(iF a) = iE(h a) ;  hy : phi(y_i) = x_i ;  hb : h(b_j) = a_j
  cert      : ZMTCert[A,F,iF,n,y,t,b] -> ZMTCert[R,E,iE,n,x,t,a]
  transport : || ZMTCert[A,F,..] || -> || ZMTCert[R,E,..] ||
  with cert-s, cert-q0, cert-q (s = phi s0, Q = mapM h Q0) and the
  evaluation naturality ZMTCertificate.Natural.mev-natural:
     phi (P(z)) = (h P)(phi z).

Residual data (ResidualAlgebra.Residual[A,setA,n]):
  t : Nat ; b : Fin t -> A ; P : Fin n -> Monic A ;
  H : Fin n -> Fin t -> Expr (Fin n).
  (R) at x in an A-algebra B: Equations[A,setA,n,D].At[B,x].Holds =
     (i) -> P_i(x_i) = sum_j iota(b_j) H_ij(x).
  F(D) = ResidualAlgebra.Algebra[A,setA,n,D] : the presented algebra of
     (n, eqs), eqs = [f_1..f_n], f_i = P_i(X_i) + (-1) sum_j b_j H_ij;
     algebra, ring, y, y-holds (U holds by construction), generated,
     To[B,a,hold].phi : Hom_A(F(D),B) with phi-y, phi-iota.

Gate B (UniversalResidualAlgebra.Over[R,setR,n,D], D over arbitrary R):
  m, c : Fin m -> R          all coefficients: b, then the lower
                             coefficients of the P_i, then the constants
                             of the H_ij, each at its own index
                             (ib, iP, iH; c-b, c-P, c-H)
  A0 = CoefficientBase.ring m = Z[C_1..C_m],  cfnA0 : CFN[Nat*Nat, A0]
  h : Hom A0 R,  h-C : h(C_k) = c_k
  D0 : Residual[A0,..,n]: b0_j = C_(ib j); P0_i = mkMonic (deg P_i)
       (C_(iP i k)) (leading 1 kept literally); H0_ij = H_ij with its k-th
       constant replaced by C_(iH i j k)
  image-b : h(b0_j) = b_j ;  image-P : h(low (P0_i) k) = low (P_i) k ;
  image-H : mapE h (H0_ij) = H_ij  (equality of expressions)
  F0 = Algebra[A0,..,n,D0]
  ToE[E,x,hold].phi : Hom F0.ring E.ring, phi-y, phi-iota (phi o iota_F0 =
       iota_E o h), from hold0 (the identities for D0 in E through h).
  No coefficient quotient on A0, no kernel of h, no F0 tensor R = E.

Gate C:
  FibreSpan.Over[A,F,iota,t,B].Finite =
     (N : Nat) * (g : Fin N -> F) * ((f : F) -> In N g f),
     In N g f = || (alpha : Fin N -> A) * Certificate f (sum_k g_k iota(alpha_k)) ||
  ResidualFibreFinite.Fibre[A,setA,n,D].finite : Finite for F(D), B = iota b,
     any A; the family is mono n y deg = the monomials y^e, e_i < deg P_i.
  CFNDescent.CFNZMT n : U (l+) =
     (K0 : U l) (A : CRing) (setA) (cfn : CFN[K0,A])
     (eqs : Equations (Fin n)) (t : Nat) (b : Fin t -> A) ->
     Instance[A,setA,n,eqs,t,b].FiniteFibre -> Instance[..].Goal
     where F = PresentedAlgebra[A,setA,(n,eqs)], FiniteFibre = Finite for
     (F, iota b), Goal = || ZMTCert[A,F,inclusion,n,generators,t,b] ||.
  CFNDescent.UniversalZMT n : U l =
     (m : Nat) (D0 : Residual[Z[C_1..C_m],..,n]) ->
     || ZMTCert[Z[C_1..C_m], F(D0), iota, n, y, D0.t, D0.b] ||
  universal-of-cfn n : CFNZMT n -> UniversalZMT n
     (Z[C] CFN by CoefficientBase.cfn, F(D0) presented by (n, eqs),
      Fibre.finite).
  CFNDescent.Descent[n,U0,R,setR,D,E,x,hold].certificate :
     || ZMTCert[R, E, iota_E, n, x, D.t, D.b] ||
  CFNDescent.DescentCFN[n,Z,...].certificate : the same from Z : CFNZMT n.

Gate D (FiniteFibreCertificates.Over[R,setR,I,Ea,n,x,gen,ff]):
  gen : (e : E) -> || (H : Expr (Fin n)) * H(x) = e ||
  ff  : FiniteFibre[R,I,E,iota] = { N ; g : Fin N -> E ;
        spans e : || Decomp N g e || },
        Decomp N g e = (alpha : Fin N -> R) * (r : E) * IEWit r *
                       (e = sum_k g_k iota(alpha_k) + r)
  residual : || ResidualIn ||,  ResidualIn = (D : Residual[R,..,n]) *
        (Holds for D at x) * ((j) -> I (D.b j))       -- no principle used
  Theorem[U0].certified : || Certified[R,I,E,iota,n,x] ||,
        Certified = { t ; a : Fin t -> R ; ina : (j) -> I (a j) ;
                      cert : ZMTCert[R,E,iota,n,x,t,a] }
  TheoremCFN[Z].certified : the same from Z : CFNZMT n.
  So: s = 1 + sum_j a_j r_j with all a_j in I, monic Q_0, Q_i over R with
  Q_0(s) = 0, Q_i(s x_i) = 0.

Usual hypothesis (QuotientFibre.Over[R,setR,I,propI,Ea]):
  I : RegularIdeal.IdealPred[R],  propI : (a) -> isProp (I.In a)
  InIE e = || IEWit[R,I.In,E,iota,e] ||   (a proposition),  IE : IdealPred[E]
  RmodI = QuotientRing[R,I,propI].ring,   pR = .projection
  EmodIE = QuotientRing[E,IE,propIE].ring, pE = .projection
  surjR q : || (r : R) * pR r = q ||,  surjE q : || (e : E) * pE e = q ||
  effective e e' : pE e = pE e' -> InIE (e - e')   (= QuotientRing.Q.effective)
  iotaI : Hom RmodI EmodIE,  iotaI-beta r : iotaI (pR r) = pE (iota r)
  Finite = ModuleFinite[RmodI,EmodIE,iotaI] = { N ; gb : Fin N -> E/IE ;
     spans q : || (ab : Fin N -> R/I) * q = sum_k gb_k iotaI(ab_k) || }
     (it contains a choice of generators, so it is not a proposition)
  bridge : || Finite || -> || FiniteFibre[R,I.In,E,iota] ||
  Gen[n,x,gen,fo].Theorem[U0].certified : || Certified[R,I.In,E,iota,n,x] ||
     for fo : || Finite ||, U0 : UniversalZMT n;  Gen[..].TheoremCFN[Z]
     the same from Z : CFNZMT n.
  Proof of bridge: the N generators are lifted once (finite choice of
  surjE, under truncation, lifts); for each element e only the N
  coefficients ab_k of its decomposition are lifted (surjR, Lifted.spans);
  pE e = pE (sum_k g_k iota(alpha_k)) (proj-eq: pE ring map, iotaI-beta),
  and effectiveness gives e - sum_k g_k iota(alpha_k) in IE (decomp).  The
  truncated Finite is eliminated directly into the propositional goal.

B and the localisation (CertificateSubalgebra, CertificateLocalisation):
  CertificateSubalgebra.Over[R,setR,Ea,n,x,s]   (any s in E)
    w = (s, s x_1, .., s x_n) : Fin (n+1) -> E   (inr tt is s)
    InB e = || (H : Expr (Fin (n+1))) * H(w) = e ||   (a proposition)
    Least[Q,..].least : InB is contained in every proposition-valued Q
       containing iota(R), the w_j, closed under + and *  (B = R[w])
    ring : CRing on (e : E) * InB e, set, eqB (equal iff equal in E),
    incl : Hom ring E, incl-inj, iotaB : Hom R ring, algebra, sB, sxB
  CertificateSubalgebra.Finite[R,setR,Ea,n,x,t,a,c]  (c : ZMTCert, s = c.s)
    finite : ModuleFinite[R, B.ring, B.iotaB]: B is spanned over R by the
       monomials w^e, e_0 < deg Q_0, e_i < deg Q_i (in B: mono-in)
  CertificateLocalisation.LocalMap[A,C,h,j]: the ring map
       phi : A[1/j] -> C[1/h j],  phi(a/j^k) = h(a)/h(j)^k,
       phi-constant: phi(a/1) = h(a)/1
  CertificateLocalisation.Iso[R,setR,Ea,n,x,s,gen]  (any s, gen as in Gate D)
    Bs = B[1/s] = PowerLocalization[B.ring, sB].ring,
    Es = E[1/s] = PowerLocalization[E, s].ring,
    phi : Hom Bs Es (LocalMap along incl),
    injective, surjective (merely a preimage), iso : Equiv Bs.R Es.R
       with iso.1 = phi.1.
  CertificateLocalisation.Consequence[R,setR,Ea,n,x,gen,t,a,c]:
    finite (B finite over R) and phi, iso (B[1/s] = E[1/s]).
  Proofs: finiteness is ResidualFibreFinite.Monomials for the ideal 0
  (w_j^d_j = - sum_k c_jk w_j^k from Q_j(w_j) = 0).  Injectivity: s^m b =
  0 in E is s_B^m b = 0 in B because incl is injective.  Surjectivity:
  e = H(x) merely and s^N H(x) in B (cleared, induction on H), so
  e/s^k = (s^N e)/s^(N+k).  Equivalence: the fibres of phi are
  propositions and merely inhabited.  The isomorphism uses only s and the
  generation of E by x; the certificate is used for finiteness.

The usual-form conclusion (FiniteFibreLocalisation.Over[R,setR,I,propI,Ea,n,x,gen,fo]):
  hypotheses: I an IdealPred with propositional membership; E generated
    by x_1..x_n (gen); fo : || QuotientFibre.Over[..].Finite || (E/IE
    finite over R/I).
  Conclusion = (s : E) * (InIE (s - 1) *
      (ModuleFinite[R, B_s, iotaB] * (InB_s s * Equiv B_s[1/s] E[1/s])))
    with B_s = CertificateSubalgebra.Over[R,setR,Ea,n,x,s] = R[s, s x_i]
    (an R-subalgebra of E: its carrier is a subtype of E, incl injective),
    and the equivalence the one of CertificateLocalisation.Iso, whose map
    is the ring map induced by B_s -> E.
  Theorem[U0].result : || Conclusion ||   for U0 : UniversalZMT n;
  TheoremCFN[Z].result : the same for Z : CFNZMT n.
  Proof: inside the truncation of QuotientFibre.Gen.Theorem, s = c.s with
  s - 1 = sum_j iota(a_j) r_j, a_j in I (Of.in-one-plus-IE), and
  CertificateLocalisation.Consequence.
  Regressions (Examples): Z/4Z with I = (2) for n = 1 and n = 0, and the
  zero fibre I = R, each from a parameter U0.


4. PROOF-TO-FILE CORRESPONDENCE
-------------------------------
  ZMTCertificate        Monic, mapM, Powers (pow, pw), Eval (mev, mev-cong),
                        HomSums, Natural (mev-natural), ZMTCert          [A]
  CertificateTransport  Gate A: cong-map, root-map, cert, transport      [A]
  FiniteFamilies        concatenation app / cat, injections, app-ind,
                        sums and combinations over concatenations       [B,D]
  CoefficientBase       Z[C_1..C_m] (tower), var, Eval.ev, ev-var, cfn   [B]
  FiniteCoefficientData mapE, along, eval-map; nc, leaf, lift, lift-image [B]
  ResidualAlgebra       Residual, Exprs (mexpr, ev-mexpr), Equations
                        (res, eqs, Holds, ev-res, zeros-of-holds,
                        holds-of-zeros), Algebra (F(D), y-holds, generated,
                        To.phi)                                         [B]
  UniversalResidualAlgebra  the universal construction (1)-(4) of §4    [B]
  FibreSpan             spans modulo (B)F: in-* lemmas, mul-closed,
                        blocks, block-in, block-ind, prod-in, Finite     [C]
  ResidualFibreFinite   Monomials (One, Claim, claim), Fibre.finite      [C]
  CFNDescent            CFNZMT, UniversalZMT, universal-of-cfn, Descent  [C]
  IdealWitnesses        IEWit, ie-* closure, VecWit, vec-of-wits         [D]
  CharacteristicMonic   Expansion (expand, CharMonic.ev-chi), Trick (the
                        determinant trick modulo IE: kernel-rel, trick-rel,
                        annih, wit)                                     [D]
  FiniteFibreCertificates  Decomp, FiniteFibre, Certified, ForZ, residual,
                        Theorem, TheoremCFN                             [D]
  ZMod4                 the ring Z/4Z (tables, laws by cases, Hedberg)  [tests]
  DescentExamples       T1-T6                                           [tests]
  QuotientFibre         IE, R/I, E/IE, iotaI, ModuleFinite, bridge, Gen
                        (the usual finite-fibre theorem)               [§7(2)]
  QuotientExamples      Q1-Q3                                           [tests]
  CertificateSubalgebra B = R[s, s x_i], Least, ring, incl, Finite.finite [§7]
  CertificateLocalisation  LocalMap, Iso (injective, surjective, iso),
                        Consequence                                     [§7]
  FiniteFibreLocalisation  the usual-form conclusion, Theorem, TheoremCFN,
                        Examples
  LocalisationExamples  L1-L3                                           [tests]
  zmt-descent.opens     the --opens audit of 58 central declarations

Informal proofs: in each file comment.  Summary:
  (A) phi(s0) = 1 + sum iota_E(a_j) phi(v_j); (h Q)(phi z) = phi(Q(z)).
  (B) record all coefficients in one family, A0 = Z[C_1..C_m], h(C_k) =
      c_k, lift; the identities (R) are the residual equations of D0 in E
      through h, so the universal property of the presentation gives phi.
  (C) modulo I0 F0, y_i^d_i is in span(1..y_i^(d_i - 1)); one-variable
      reduction, then products variable by variable (blocks), then every
      expression e(y) multiplies the span into itself; f = e(y).1.
      Apply the principle over A0 and transport along (h, phi).
  (D) determinant trick modulo IE for each x_i (Cayley-Hamilton matrix of
      the decompositions of x_i g_k), chi(x_i) in IE; one common family in
      I for the n memberships (concatenation); expressions for the
      multipliers by algebra generation; this is (R); apply (C).


5. TRUNCATIONS
--------------
Only finite data are chosen, always under truncation and eliminated into
truncated (propositional) goals: the decompositions of x_i g_k and of 1
(fchoice over Fin N), the monic equations for i : Fin n (fchoice), the
expressions H_ij (fchoice over i and j), the representatives of elements
of F(D) (PresentationExistence.generated) in Fibre.spans, and the
certificate returned by the principle.  The congruence of a certificate
is an explicit FiniteIdeal certificate (v_j with s = 1 + sum b_j v_j):
this is membership of s - 1 in the extended ideal (b)F by definition, so a
future theorem returning only membership "s - 1 in I0 F" with I0 = (b)
supplies it by unfolding (FiniteIdeal is exactly finitely generated ideal
membership).  No global section of a quotient or image is used.


6. REGRESSIONS (DescentExamples)
--------------------------------
  T1  a supplied certificate over Z (n = t = 0; s = 1, Q0 = T - 1)
      transported to Z/4Z: s = 1, Q0 = T + 3, by computation.
  T2  residual data over the NONREDUCED ring Z/4Z: x = 2 (2*2 = 0),
      b = (2), P = T^2 with lower coefficients 0, 0 (REPEATED), H = 0.
      m = 4; the two 0 coefficients are recorded at DIFFERENT indices
      (distinct) and both sent to 0 by h (h NOT injective: image0, image1;
      no kernel coherence used); image-b, image-H; A0 CFN; phi(y) = 2;
      special fibre of F0 spanned by 2 monomials (fibre-size, finite).
  T3  n = 0, t = 0 over Z: the fibre is spanned by 1; Descent applies.
  T4  RESIDUAL-ZERO case: P = 1 (degree 0), 1 = 1 * 1: the spanning family
      is empty and 1 is in I0 F0 (one-in-ideal).
  T5  ACTUAL TRANSPORT through a residual algebra: F = Z[C][y]/(y - C);
      certificate s = 1, Q0 = T - 1, Q1 = T - C, proved in F (y = C from
      y-holds); carried along C |-> 2, phi : y |-> 2 to Z/4Z: s = 1,
      Q0 = T + 3, Q1 = T + 2 (q0-is, q1-is, s-is); the annihilations are
      the transported proofs.
  T6  Gate D on Z/4Z, I = (2), E = Z/4Z, x = 2, fibre spanned by 1:
      residual data with (R) extracted with no principle (residual), and
      the certified conclusion from a parameter U0 : UniversalZMT 1.
QuotientExamples (the usual hypothesis):
  Q1  NONREDUCED base: R = E = Z/4Z, I = (2) (a proposition, by cases),
      x = 2; 2 is 0 in R/I and E/IE; E/IE spanned over R/I by the class
      of 1; bridge gives || FiniteFibre ||; certified from UniversalZMT 1.
  Q2  EMPTY family of algebra generators (n = 0): the same, certified from
      UniversalZMT 0.
  Q3  ZERO fibre: I = R, so IE = E (1 in IE), E/IE = 0 spanned by the empty
      family (N = 0); bridge and certified conclusion from UniversalZMT 1.
LocalisationExamples (B and B[1/s] = E[1/s]):
  L1  the transported certificate of T5 over Z/4Z (s = 1, x = 2): B spanned
      by one monomial; the isomorphism.
  L2  NILPOTENT s = 2 over Z/4Z (x = 1, 2 = 1 + 1*1, Q0 = Q1 = T + 2, by
      computation): E[1/2] = 0; B finite and the isomorphism still hold.
  L3  n = 0, s = 1, Q0 = T + 3: B finite, the isomorphism.


7. REMAINING OBLIGATIONS
------------------------
  (1) The CFN-base ZMT certificate principle itself (CFNZMT n, or only
      UniversalZMT n) is NOT proved here.  It is to be supplied by the
      separate ZMT4/Rees development for n <= 3 (sag/zmt-rees4 and the
      ZMT4 work), and for arbitrary n by the generic proof
      (sag/zmt-cech-general, sag/zmt-syzygies-general).  The
      four-coordinate development is not claimed to give arbitrary n.  The
      future theorem must be put in the form CFNZMT n: finitely presented
      algebra over a CFN ring, special fibre spanned modulo (b)F with
      coefficients in A, truncated certificate with explicit congruence.
      If it is stated with a quotient module F/I0F over A/I0, the bridge is
      the lifting of finitely many coefficients along A -> A/I0
      (surjective under truncation); that bridge is not formalised here.
  (2) DONE (QuotientFibre): the usual hypothesis "E/IE is finite over
      R/I" (quotient rings, induced structure map, finite generation as a
      module, under truncation) gives the elementwise FiniteFibre, and the
      certificate theorem holds with it.  Remaining integration: a caller
      whose E/IE or R/I is a different quotient construction (another
      quotient module or ring API) needs an isomorphism to QuotientRing's,
      or a restatement of ModuleFinite through it; the same lifting
      argument then applies.  Also the bridge assumes I is an IdealPred
      with propositional membership; a non-propositional ideal predicate
      should be truncated first.
  (3) DONE (CertificateSubalgebra, CertificateLocalisation): B finite over
      R and B[1/s] = E[1/s].  Not provided: the inverse of phi is not
      packaged as a ring map (it is one, as the inverse of a bijective ring
      map), and the universal property of B[1/s] is not stated.  The
      composite from the usual finite-fibre hypothesis to (s, finite B,
      B[1/s] = E[1/s]) is FiniteFibreLocalisation.Theorem.
  (4) Representation bridges not needed by the descent and not provided:
      Monic -> a monic element (Lead d p 1) of PolynomialRing.Extension
      (only the converse direction, chi -> Monic, is proved); expressions
      Expr (Fin n) versus the iterated ring A[X_1]..[X_n] of
      sag/zmt-syzygies4.
  (5) Nothing is committed.
