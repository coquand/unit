sag/zmt-syzygies4: homogeneous syzygies of four-variable polynomials
constructed from CFN coherence, and the dependence theorem without a
supplied syzygy hypothesis
=====================================================================

Task: doc/zmt-homogeneous-syzygies-handoff.txt, doc/zmt-homogeneous-syzygies-command.txt.
Builds on sag/zmt-lifting (Stages 1, 2) and sag/zmt-lifting-general (the
general four-coordinate certificate), reused through relative links,
UNCHANGED.

STATUS (30 October 2026).  Gates A-D and the regression instances are
formalised and checked.  The final theorem's hypotheses are only a CFN
set-ring D, the finite homogeneous input g with its degrees, the sequence c
and its truncated cocycle witnesses.  No syzygy matrix, Identity or SyzGen
is assumed anywhere.  Not committed to git.

Check:   ./segc sag/zmt-syzygies4 all                         (from unit/)
Fresh:   cd sag/zmt-syzygies4 && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-syzygies4.opens


1. FOUNDATIONS, ASSUMPTIONS, FILES
----------------------------------
All.seg is the segment Theory of sag/ (as in sag/zmt-lifting-general):
parameters univ (univalence), images (replacement) and surjections;
fe (FunExt) and propUA are derived.  Truncation = Truncation.Trunc.  No new
axioms: no choice, excluded middle, SAG/SQC, resizing or noetherian axiom;
no new Theory parameter.  The checker is unchanged.  One universe level l.
The only finite choices are Trunc-eliminations over Fin n
(LaurentSyzygyLift4.fin-choice), always into a truncated goal.

New files (639 declarations):
  FinitePolynomial4       cf p = p 1, its laws, coef p = cf p on N^4,
                          finitely supported coefficient functions as term lists
  PolynomialRing4Bridge   S = D[X_0][X_1][X_2][X_3]; phi : term lists -> S,
                          psi : S -> coefficient functions; the bridges
  WeightedParts4          degree parts, shifted-degree filters, the
                          decomposition, ranges 0..B, pairs of indices
  UngradedSyzygies4       Gate B: finite ungraded syzygies from coherence of S
  HomogeneousSyzygies4    Gate C: the homogeneous matrix H, Identity, SyzGen
  CoherentDependence4     Gate D: the final theorem
  SyzygyRegression4       the regression instances
  All.seg, README.txt, zmt-syzygies4.opens
Links (relative, to the real targets): all links of sag/zmt-lifting-general
(same targets), its own nine files as ../zmt-lifting-general/X.seg, and the
HilbertCFN chain of sag/artin-rees resolved to the original files
(AffineRing, AffinePowers, PolynomialCoefficients, PolyPres, Hilbert,
Transfer, Blocks, SeqPoly, XSpan, Saturation, DegreeCor, PolyCoef, HilbertD,
FinCat, Schreyer, HilbertC, HilbertCFN).  No shared file was modified.


2. THE FINAL THEOREM (Gate D)
-----------------------------
CoherentDependence4.Over[K0,D,setD,cfn].Input[a,d,g,hg].Seq[c,lift].dependence
Parameters:
  K0 : U l ;  D : CRing ;  setD : isSet D.R ;  cfn : CFN.CFN K0 D ;
  a : Nat ;  d : Fin a -> Base.Nat ;  g : Fin a -> PolynomialAction4.TPoly D.R ;
  hg : (i : Fin a) -> HomogeneousMatrices4.HomDeg D.R (d i) (g i) ;
  c : Nat -> F1.E0.El                        (= C^1(-1), Cech4 edges) ;
  lift : (n : Nat) -> || Lifted (c n) ||, where
    Lifted c = (u : F2.E1.El) * Id (D1.d0.f c) (F2.A.f u)
    i.e. merely u_i in C^2(-1-d_i) with  delta c_n = sum_i g_i u_i .
Conclusion:  || Result ||,
  Result = (qs : List D.R) * Bdry (rest qs),
  rest qs = c_(len qs) - sumL qs,   sumL [] = 0,  sumL (q::qs) = q c_(len qs) + sumL qs,
  Bdry x = (h : F0.E0.El) * (a' : F1.E1.El) * Id x (D0.d0.f h + F1.A.f a'),
i.e. merely N = len qs (N = 0 allowed), q_0..q_(N-1), h in C^0(-1),
a_i in C^1(-1-d_i) with
     c_N - sum_{k<N} q_k c_k = delta h + sum_i g_i a_i .
F0, F1, F2, D0, D1 are the families of M0 = (a, 0, d, -, g, -, hg, -), the
original input with NO column: A y = sum_i g_i y_i by definition
(HomogeneousMatrices4.Fam.A-val), delta = Cech4.D0, D1.  They mention only
a, d, g, hg.
Proof: HomogeneousSyzygies4.Gens.Of.homogeneous merely gives b, e, H, hH,
Identity M, SyzGen M for M = (a, b, d, e, g, H, hg, hH) (Gate C).  For such
data the ALREADY CHECKED ResolutionDependence4.Over.Dep[M,ah,syz].Seq gives
the conclusion for the families of M; the types are those of M0 by
computation (named transports FromData.lift' and FromData.back, checked
once), and its finite sum is sumL (FromData.sumL-same, induction on qs).
The truncation of the constructed data is eliminated into the truncated
conclusion (TC.bind); q, h, a remain witnesses under the truncation.


3. GATE A: POLYNOMIAL REPRESENTATIONS (FinitePolynomial4, PolynomialRing4Bridge)
------------------------------------------------------------------------------
Iteration order: S1 = D[X_0], S2 = S1[X_1], S3 = S2[X_2], S = S3[X_3]
(PolynomialRing4Bridge.Over: L1..L4 = Level[..], S = L4.T, each the quotient
ring PolynomialRing.Extension, i.e. the ring of PolyCoef/HilbertCFN).
Coordinate u_k of an exponent (N4 or Z^4) is the exponent of X_k; X_0 is the
variable of the innermost ring.  X0..X3, cst c (the constant), pw (powers).

Coefficient function of a term list (FinitePolynomial4.Over):
  delta0 = 1 at 0, 0 elsewhere;  cf p m = PA.mulP p delta0 m.
  cf-pmul : cf (p q) = p (cf q);  cf-psum, cf-app;
  cf-neg  : cf p vanishes at exponents with a negative coordinate;
  cf-supp : cf p vanishes outside suppL [0] p;
  cf-van  : Shifts 0 k p -> cf p vanishes off degree k;  polEl : chart element;
  coef-cf : PA.coef p v = cf p (emb v)  for v in N^4;
  cz-of-cf / cf-of-cz : CoefZero p  iff  cf p = 0.

Maps and bridges (PolynomialRing4Bridge.Over):
  phi : TPoly D.R -> S,  phi p = sum c X_0^u0 X_1^u1 X_2^u2 X_3^u3  (term)
    phi-app (zero: by definition), phi-pmul (term-mul), phi-psum,
    phi-scale : phi (c p) = cst c phi p   (D-scalars).
  psi : S -> Z^4 -> D, psi s m = coefficient of X^m (0 off N^4), composed
    from Level.at (at x i = coefficient of T^i): psi-add, psi-zero,
    psi-scale, psi-X0..X3 (X_k shifts), psi-one (= delta0; one-sel).
  ext4          : psi s = psi s' -> s = s'        (coefficient extensionality)
  psi-phi       : psi (phi p) = cf p              (THE bridge)
  phi-eq-of-cf / cf-eq-of-phi : cf p = cf q  iff  phi p = phi q
  phi-eq-of-coef / coef-eq-of-phi : equal N4-coefficients iff equal images
  phi-zero-of-cz / cz-of-phi : CoefZero p iff phi p = 0
  rep : (s : S) -> || (p : TPoly) * phi p = s ||   (every element merely
    has a term list: Level.gen at the four levels, the property is closed
    under +, under X_k . (bump_k) and contains the constants)
  coefficient-rep / FinitePolynomial4.cf-rep : a coefficient function f
    vanishing outside a list s (repetitions allowed) and at negative
    exponents is cf p, and psi (phi p) = f.  Construction: deduplicate s
    (Nub over dec-e4), keep the members in N^4 (classify), one term f(m) X^m
    each; each coefficient is counted once (sel-single); no coefficient of
    D is ever tested.
  Syzygy transfer (UngradedSyzygies4.Gens): phi-prod, cf-prod,
    syz-to-S / syz-from-S : USyz y iff (phi y_i) is a syzygy of (phi g_i).
Proved: phi is additive and multiplicative, preserves D-scalars, is merely
surjective (rep), and phi p = phi q iff p, q have the same coefficients.  An
explicit equivalence (term lists mod coefficients) ~ S is NOT stated as such.


4. GATE B: UNGRADED SYZYGIES (UngradedSyzygies4)
------------------------------------------------
Over[D,setD].Gens[a,g]:
  prod y = sum_i g_i y_i ;  USyz y = CoefZero (prod y) ;
  CombW p h y = (c : Fin p -> TPoly) * ((i) -> CoefEq (y i) (sum_k h_k,i c_k)) ;
  UComb p h y = || CombW p h y || ;
  UngradedW = (p : Nat) * (h : Fin p -> Fin a -> TPoly) * ((k) -> USyz (h k))
              * ((y) -> USyz y -> UComb p h y).
THEOREM Gens.Of[K0,cfn].ungraded : || UngradedW ||   (D CFN).
  cfnS : CFN K0 S = HilbertCFN.poly four times.  Coherent.Coh of S for the
  row u_i = phi g_i (single-row coherence, no resolution); the finitely many
  entries of the generators and of the coefficients of a combination are
  pulled back to term lists by rep, inside the truncation (fin-choice).


5. GATE C: HOMOGENEOUS SYZYGIES (WeightedParts4, HomogeneousSyzygies4)
---------------------------------------------------------------------
Columns[w] (w : UngradedW):
  B = sum_k sum_i bnd d_i h_k,i  (bounds d_i + size u of all terms; bounded)
  columns j = (k, e), k < p, e = 0..B:  b = mulF (B+1) p, colK, colE (decode)
  e_j = colE j ;  H_i,j = filt d_i e_j h_(colK j),i ;  hH by filt-hom.
  M = mkMatrices D a b d colE g H hg hH  (the ORIGINAL a, d, g, hg; g is
  kept as given, never normalised).
(a) hH : HomShift d_i e_j H_ij, termwise (strong form).
(b) WeightedParts4.decomp : sum_{e=0..B} (filt dd e h) f = h f (for BoundT);
    range-single: sum_{e=0..B} [x = e] c = c for x <= B.
(c) Columns.ah : HM.Identity M.  Col.zero: cf P_e = sum_e' part e (cf P_e')
    = part e (cf P) = 0 (PeHom: cf P_e homogeneous of degree e; sum-Pe; SelPart).
(d) Columns.generate : USyz y -> UComb b (columns) y  (Generate.at:
    cf y_i = sum_j H_ij (cf c_(colK j)), via decomp and sum-pair).
(e) Columns.syz : LaurentSyzygyLift4.Over.SyzGen M, the EXACT existing
    homogeneous interface, for every n : Int.  Extract[n,y,sy]: support
    witnesses (fin-choice), cf-rep, usyz (A y = 0), generate, and
    z_j = partEl (n - e_j) (cf c_j) = part (n - e_j) (cf c_j) in the
    polynomial chart of degree n - e_j; Row.pt: (H z)_i = y_i by
    WeightedParts4.mulP-part (p (part k f) = part k' (p f) when every term
    goes from k to k'), part-sum, part-id.
Negative degrees: nothing excludes n - e_j < 0 or n - d_i < 0: part k for
k < 0 is computed like any other (a homogeneous polynomial of negative
degree is 0 since it also vanishes at negative exponents), partEl carries
its support list and degree witness for every k : Int (regression ex5).
Export:  Gens[a,d,g,hg].SyzData = (b : Nat) * (e) * (H) * (hH)
           * Identity (mkMatrices D a b d e g H hg hH) * SyzGen (same) ;
         accessors SD[x].{b,e,H,hH,M,ah,syz} ;
THEOREM Gens.Of[K0,cfn].homogeneous : || SyzData ||.
No domain, field, regularity or degree hypothesis on D; zero columns kept.


6. REGRESSION INSTANCES (SyzygyRegression4)
-------------------------------------------
Over any commutative set-ring D (Over[D,setD]), and over Z (OverZ, ZCFN):
  inputs   1. g = (X_0^3, X_1^3), d = (3,3)        (CubicResolution4.g, hg)
           2. g = (X_0^3 + X_1^3, X_1^3), d = (3,3) (PolynomialPairExample4.g2)
           3. g = (X_0, X_0), d = (1,1)            (g3, hg3)
           4. the empty list, a = 0               (g4)
           5. g = (0) (empty term list), d = (5)  (g5)
  Dep[K0,cfn].dep1..dep5 : the Gate D theorem for each input (D CFN);
  OverZ.dep1, dep3 : over Z.
  Ex[K0,cfn].lifted1..6 : the CONSTRUCTED SyzGen applied to concrete
    homogeneous syzygies: merely constructed data x with z, H z = y:
      ex1 y = (-X_1^3, X_0^3), n = 6       (syzygy from CubicResolution4.id1)
      ex2 y = (-X_1^3, X_0^3+X_1^3), n = 6 (from PolynomialPairExample4.id2)
      ex3 y = (-1, 1), n = 1               (weighted column with constant
                                            entries; sy3 by one decision)
      ex4 y = (1) for g = (0), n = 5
      ex5 y = (0, 0) for input 1, n = 1    (degrees 1 - 3 < 0)
      ex6 the empty vector, a = 0, n = 0
  OverZ.lifted3 : ex3 over Z.
The old hand-written SyzGen proofs (CubicResolution4.syz1,
PolynomialPairExample4.syz2) are NOT used; only the data g, hg and their
checked Identity (to certify the concrete syzygies y) are reused.  No
canonical output of the coherence algorithm is compared.
Mutation tests (restored afterwards): y3 = (1, 1) instead of (-1, 1) makes
sy3 fail; the degree 5 instead of 6 in ex1 makes ex1 and lifted1 fail.


7. VALIDATION
-------------
  timeout 55 ./segc sag/zmt-syzygies4 all
      101 modules, 0 failed, OK  (2.2 s warm server; new files 0.02-0.32 s)
  cd sag/zmt-syzygies4 ; timeout 55 $(cabal list-bin exe:seg) All.seg
      All.seg: 5992 declarations, 0 failed, 2.44 s, OK
      (5353 = the reused tree incl. the HilbertCFN chain; 639 new)
  ... All.seg --opened : every new declaration <= 0.05 s, at most 45
      definitions opened (HomogeneousSyzygies4 Row.pt, Stage 2 max was 1957).
      New declarations per file: FinitePolynomial4 82, PolynomialRing4Bridge
      142, WeightedParts4 98, UngradedSyzygies4 62, HomogeneousSyzygies4 103,
      CoherentDependence4 49, SyzygyRegression4 103.
  ... All.seg --opens zmt-syzygies4.opens
      93 declarations: "nothing else opened" for each.  The lists name the
      notions of each proof and the carriers; in PolynomialRing4Bridge the
      operations of the quotient ring S are unfolded down to
      PolynomialRing's aliases (mulQ = Multiply.operation, Quot.Descend),
      a representation cost (<= 0.05 s), see the file header.
  Older developments, unchanged, rechecked fresh:
      sag/zmt-lifting-general/All.seg : 4231 declarations, 0 failed, 1.35 s
      sag/zmt-lifting/All.seg         : 3338 declarations, 0 failed, 0.93 s
  No body-less declaration (parameter) in the new files.


8. REMAINING OBLIGATIONS AND SCOPE
----------------------------------
Within this milestone: none of the requested constructions is assumed.
Limits, stated honestly:
  * the bridge proves maps, coefficient extensionality and truncated
    representation; an explicit ring equivalence (term lists modulo
    coefficient equality) ~ S is not packaged;
  * the column set is generous: all pairs (k, e) with e <= B, B a sum of
    all shifted degrees, so many columns are zero (allowed by the handoff);
  * the .opens specification covers 93 central declarations of 639;
  * in PolynomialRing4Bridge, comparisons through S open the operation
    aliases of the quotient ring (S = L4.T = Extension.ring); harmless in
    time, but more than the text says; removing the aliases would need
    changes in sag/polynomial, which this task does not touch.
OUT OF SCOPE (not proved here): full ZMT; arbitrary dimension (four
coordinates only) and arbitrary projective dimension; Rees comparison and a
second (Rees) grading; weighted/Rees dependence; finite-fibre sections;
terminating free resolutions / Hilbert syzygy theorem (not needed).
