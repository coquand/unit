sag/zmt-weighted4: weighted dependence for the four-coordinate Cech
development, by projecting the final identity of CoherentDependence4
=====================================================================

Task: doc/zmt-weighted-dependence-handoff.txt, doc/zmt-weighted-dependence-command.txt.
Builds on sag/zmt-syzygies4 (CoherentDependence4, reused UNCHANGED) and,
through it, on sag/zmt-lifting-general and sag/zmt-lifting, all reused by
relative links.

STATUS (30 October 2026).  Gates A-D and the regression instances are
formalised and checked.  The coefficient ring D = A[U_1..U_t], its grading,
its CFN structure and its evaluations are CONSTRUCTED; the weighted theorem
is obtained by projecting the conclusion (U) of the checked
CoherentDependence4.  No syzygy, weighted-dependence or ideal-power
statement is assumed.  Not committed to git.

Check:   ./segc sag/zmt-weighted4 all                         (from unit/)
Fresh:   cd sag/zmt-weighted4 && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-weighted4.opens


1. FOUNDATIONS, ASSUMPTIONS, FILES
----------------------------------
All.seg is the segment Theory of sag/ (as in sag/zmt-syzygies4): parameters
univ (univalence), images (replacement) and surjections; fe (FunExt) and
propUA are derived.  Truncation = Truncation.Trunc.  No new axioms: no
choice (not even finite choice in the new files), no excluded middle, no
SAG/SQC, no resizing, no new Theory parameter.  The checker is unchanged.
Decisions are made only on integers (int-dec, coefficient degrees) and on
exponents (dec-e4, in a regression), never on coefficients of A or D.  No
field, domain or nontriviality hypothesis on A.

New files (641 declarations; no body-less declaration except the fields of
the record type Graded, which is always instantiated by constructions):
  CoefficientParts        degrees (lowerZ, subZ, cdeg), the record Graded,
                          its laws (Laws), finite expressions (Expr)
  CoefficientPolynomial   Gate A: base grading on A, the step R -> R[U],
                          the tower D_t = A[U_1..U_t], CFN of D_t
  CoefficientCech4        Gate B: Pr_k on chart cochains, delta commutes
  BihomogeneousAction4    Gate B: CoefHom, Pr_k (g a) = g Pr_(k-f) a, families
  WeightedDependence4     Gate C: the weighted theorem
  FiniteIdealPowers       I^k M for a finite generator list (t >= 0)
  CoefficientEvaluation4  Gate D: evaluation, witnesses, evaluated identity
  WeightedRegression4     regression instances
  All.seg, README.txt, zmt-weighted4.opens
Links: the same relative targets as sag/zmt-syzygies4, and its own seven
files as ../zmt-syzygies4/X.seg.  No shared or earlier file was modified.

Two kinds of integer degrees are kept apart in names and prose:
PROJECTIVE degrees (Laurent4.deg, the twists -1, -1-d_j, minus n d_i) and
COEFFICIENT degrees (U-degree: pr k, Hom k, cdeg, lowerZ, subZ).  List
indices and coefficient indices are natural numbers (Ring.Nat); toB maps
them to the naturals of Int, cdeg n = pos (toB n), lowerZ k i = k - i,
subZ k e = k + (-e).


2. THE THEOREMS
---------------
(C) Weighted dependence, concrete form:
  WeightedDependence4.Concrete[K0,A,setA,cfnA,t].W
     .Input[a,d,f,g,hg,hf].Seq[c,hc,lift].dependence : || WResult ||
  (generic form: WeightedDependence4.Over[K0,A,t,D,setD,G,cfn].Input..Seq..dependence
   for any CFN set-ring D with a grading G : Graded A t D; Concrete takes
   D = T.D t, G = T.grD t, cfn = T.cfnD K0 cfnA t of CoefficientTower.)
Parameters:
  K0 : U l ;  A : CRing ;  setA : isSet A.R ;  cfnA : CFN K0 A ;  t : Nat ;
  a : Nat ;  d, f : Fin a -> Base.Nat  (projective / coefficient degrees) ;
  g : Fin a -> TPoly D.R  (term lists in X_0..X_3 with D-coefficients) ;
  hg : (i) -> HomDeg D.R (d i) (g i)            (projective homogeneity) ;
  hf : (i) -> CoefHom (f i) (g i)               (every coefficient of U-degree f_i) ;
  c : Nat -> C^1(-1)  (= CI.F1.E0.El, the CoherentDependence4 families) ;
  hc : (n) -> DF.P1.Hom (cdeg (suc n)) (c n)    (c_n of coefficient degree n+1) ;
  lift : (n) -> || Lifted (c n) ||  exactly CoherentDependence4's hypothesis:
         merely u_n,j in C^2(-1-d_j) with delta c_n = sum_j g_j u_n,j
         (no coefficient degree prescribed for u; no chosen sequence).
Conclusion WResult = (rs : List D.R) * WBdry (len rs) rs, with
  WBdry N rs = (v : C^0(-1)) * (a' : prod_j C^1(-1-d_j))
     * DF.P0.Hom (N+1) v              v of coefficient degree N+1
     * FP.Hom (N+1) a'                a'_j of coefficient degree N+1-f_j
     * HomL N rs                      r_i of coefficient degree N-i
     * Id (c_N - sumL rs) (delta v + sum_j g_j a'_j)                  (W)
  rs = [r_(N-1), .., r_0]; sumL [] = 0, sumL (r :: xs) = r c_(len xs) + sumL xs
  (CoherentDependence4's own sum); HomL N (x :: xs) = Hom (N - len xs) x * HomL N xs.
  Accessors: WR[w].{rs,N,v,a',hom-v,hom-a,hom-r,eq}.
  v keeps projective twist -1, a'_j keeps -1-d_j (same types as in (U)).
  N = 0 and rs = [] are allowed (v then has coefficient degree 1); a
  negative N+1-f_j is allowed (a'_j is then 0, Pr of negative degree).

(D) Evaluated form:
  CoefficientEvaluation4.Concrete[K0,A,setA,cfnA,t,a].ED
     .Input[na,d,f,g,hg,hf].Seq[c,hc,lift].evaluated : || EvResult ||
  (a : Fin t -> A.R the values of U_1..U_t; na the number of g_j.)
  EvResult = (w : WResult) * EvBdry w, where EvBdry w is
     ev c_N - sum_{i<N} ev(r_i) ev c_i = delta (ev v) + sum_j ev(g_j) ev(a'_j)
       (in the cochain modules of CoherentDependence4 over A for the
        evaluated polynomials ev(g_j) = evT (g j), same d_j: CIA.F1, CIA.D0)
   * PowL N rs : ev(r_i) in I^(N-i) (WitZ, explicit witnesses)
   * Wit (N+1) (ev v) in the chart module C_A^0(-1) (explicit witness)
   * for every j, WitZ (N+1-f_j) (ev a'_j) in C_A^1(-1-d_j).
  I = (a_1, .., a_t).  The terms ev(g_j) ev(a'_j) are KEPT in the equation.

Proof of (C) (WeightedDependence4.Over.Input.Seq):
  CS.dependence (CoherentDependence4, unchanged) merely gives qs, h, a with
     c_N - sum_{i<N} q_i c_i = delta h + sum_j g_j a_j,  N = len qs.    (U)
  Project[res]: apply Pr (N+1) on C^1(-1) (W-eq):
     Pr (N+1) c_N = c_N                            proj-hom, hc N
     Pr (N+1) (sumL qs) = sumL (projL N qs)        sum-proj, term-proj
         (Pr (N+1) (q c_i) = pr ((N+1)-(i+1)) (q) c_i = pr (N-i) (q) c_i)
     Pr (N+1) (delta h) = delta (Pr (N+1) h)       CoefficientCech4.Diff.D0-proj
     Pr (N+1) (sum_j g_j a_j) = sum_j g_j Pr (N+1-f_j) a_j   FamPr.A-proj
     Pr additive (proj-sub, proj-add).
  r_i = pr (N-i) q_i, v = Pr (N+1) h, a'_j = Pr (N+1-f_j) a_j; their
  homogeneity is pr-idem (hom-projL, hom-proj).  projL N uses the FIXED
  outer N = len qs at every entry (the entry with tail length i gets
  pr (N - i)); len-proj : len (projL N qs) = len qs transports (W) to
  N = len rs.  The truncation of (U) is mapped (TC.map) into || WResult ||.
  q, h, a are NOT assumed homogeneous; no syzygy is built here.

Proof of (D) (CoefficientEvaluation4.Over.EvDependence.Input.Seq.Ev):
  evc (pointwise ev) is additive and evc (q x) = ev(q) evc x, so
  evc (sumL rs) = sumA rs (ev-sumL); evc o delta = delta o evc (ev-D0);
  evc (sum_j g_j y_j) = sum_j ev(g_j) evc y_j (ev-A, from ev-mulP).
  Applying evc to (W) gives the evaluated identity (Ev.eq).  Witnesses:
  powL (scalars, witZ-scalar), EvChart.wit / witZ (cochains), below.


3. GATE A: THE COEFFICIENT RING AND ITS PROJECTIONS
---------------------------------------------------
Generic notion (CoefficientParts.Graded A t R): fields pr, pr-add, pr-idem,
pr-orth, pr-negdeg, pr-mul, iota, iota-hom, base, base-eq, var, var-hom,
low, low-zero, low-hom, low-eq, ev, ev-iota, ev-var (see the file header).
Hom k x := pr k x = x (allows 0 in every degree; hom-negdeg: for k < 0
only 0).
Laws[A,t,R,setR,G] (the bullets of handoff §4):
  additive: pr-add (field), pr-zero, pr-neg, pr-sub, pr-sum (finite sums);
  A-linear: pr-iota  (pr k (iota a . y) = iota a . pr k y);
  pr k x homogeneous of degree k: hom-pr;  Hom k x gives pr k x = x: by
  definition;  Hom e x, k /= e gives pr k x = 0: hom-other;
  y of degree e: pr k (x y) = pr (k-e) (x) y: pr-mul (field), pr-mul-pos;
  homogeneous factor first: pr-mul-left, pr-mul-pos-left;
  hom-add, hom-sum, hom-mul (degrees add), hom-iota, hom-one;
  finite expression with all monomials of degree k:
    Expr 0 = A, Expr (k+1) = Fin t -> Expr k ;
    value 0 a = iota a, value (k+1) e = sum_j var j . value k (e j)
    (= sum over words j_1..j_k of var j_1 ... var j_k iota (a_w));
    value-hom : value e has degree k;  expr k x h : Expr k for x of degree
    k (canonical, no truncation needed);  expr-value : value (expr x) = x.
    This is the nested (Horner-word) form of a finite polynomial
    expression; a flat list of exponent vectors is not formalised.
Construction (CoefficientPolynomial):
  BaseGrading[A,setA].graded : Graded A 0 A:  pr k a = a if k = 0, else 0
    (keep, one decision int-dec k 0); var/low over Fin 0 empty; an element
    of degree k+1 is 0 (low-eq); ev a = identity.
  GradingStep[A,setA,t,R,setR,G].graded : Graded A (t+1) R[U]:
    R[U] = PolynomialRing.Extension[R,setR].ring (the quotient ring of
    PolyCoef/HilbertCFN);  pr k on lists (mapP) descended to the quotient
    (PD.DD); coef-pr : (pr k x)_i = pr (k - i) (x_i); laws coefficientwise
    by PolynomialCoefficients.ext (sub-lower: (k-i)-(e-i) = k-e,
    lower-ne); pr-mul by induction on a degree bound (MulBy.bounded:
    PolyCoef.mul-hor, pr-cmul, pr-X, horner); var (inl j) = var j as a
    constant, var (inr tt) = U; low (inl j) x = low j (x_0), low (inr tt)
    x = tail x; low-eq: x = U tail x + sum_j var j low j (x_0); ev from
    Universal.Property.Given (U_(t+1) |-> a (inr tt)).
  CoefficientTower[A,setA]:
    tower : (t : Nat) -> Level t,  Level t = (R : CRing) * isSet R.R * Graded A t R
    D t, setD t, grD t (accessors); D-suc : D (t+1) = D_t[U] by definition;
    cfnD K0 cfnA : (t) -> CFN K0 (D t)  (HilbertCFN.poly at each step).
  Variable order: D_0 = A, D_(t+1) = D_t[U_(t+1)]; U_1 is the variable of
  the innermost ring; index inl j = old variable, inr tt = the new one.
  t = 0 is included (D_0 = A).


4. GATE B: PROJECTIONS ON THE FOUR-CHART COCHAINS
-------------------------------------------------
CoefficientCech4.Over[A,t,D,setD,G].ChartPr[I,Bad] (any chart module of
Laurent4, so every Cech degree and every projective twist):
  proj k x : (Pr k x)(i)(m) = pr k (x(i)(m)), the SAME support list
    (vanish) and vanishing set (van) — finite support and the
    chart / projective-degree conditions are kept;  proj-val (refl);
  Hom k x = every coefficient of degree k (independent of the projective
    degree);  hom-proj, proj-hom, hom-zero;
  proj-add, proj-zero, proj-neg, proj-sub, proj-sum (finite sums),
  proj-iota (A-linearity);  NOT D-linear (none is claimed);
  scalar action: proj-scalar  Pr k (q x) = pr (k - e)(q) x  for x of
    degree e;  proj-scalar-pos (e = pos n).
  Diff[n].D0-proj, D1-proj, D2-proj : Pr k (delta x) = delta (Pr k x)
    (pointwise shapes x - y, (x - y) + z, ((x - y) + z) - w).
BihomogeneousAction4.Over[A,t,D,setD,G]:
  CoefHom f g : every coefficient of every term of g has U-degree f;
  mulP-proj : pr k ((g F)(m)) = (g (pr (k-f) o F))(m)  (termwise, by
    pr-mul-pos-left; no Cech contraction is involved);
  Act[..].act-proj : Pr k (g a) = g Pr (k - f) a  on charts, any twists;
  FamPr[M,f,hf,I,set,n] : (Pr k y)_i = Pr (k - f_i) y_i on
    prod_i C(n - d_i); Hom; hom-proj; gi-proj; A-proj : Pr k (A y) = A (Pr k y).
  The scalar action (q in D) and the polynomial action (g in X_0..X_3)
  are separate lemmas with separate names.


5. GATE D: EVALUATION AND FINITE IDEAL POWERS
---------------------------------------------
FiniteIdealPowers.Over[A,Md,t,a]: gen xs = sum_j a_j x_j (Comb.comb);
  Step P x = (xs) * ((j) -> P (xs j)) * (x = gen xs);
  Wit 0 x = Top, Wit (k+1) = Step (Wit k)        explicit witnesses;
  Pow 0 x = Top, Pow (k+1) x = || Step (Pow k) x ||  membership
    (x in I^(k+1) M iff merely x = sum_j a_j x_j with x_j in I^k M);
  pow-prop, wit-pow, wit-tr, wit-zero;  WitZ / PowZ k: I^n for k = pos n,
  {0} for k < 0;  witZ-powZ.  t = 0 allowed (then I^(k+1) M = 0).
CoefficientEvaluation4.Over[A,setA,t,D,setD,G,a]:
  ev = G.ev a (for the tower: iterated universal properties, ev-var:
    U_j |-> a_j, ev-iota);  ev-comb : ev (sum_j var j y_j) = sum_j a_j ev y_j;
  scalars: wit-value (the evaluated expression is the witness tree),
    wit-scalar k x : Wit k (ev x) for x of degree k >= 0 (through
    expr/expr-value), witZ-scalar (k < 0: ev x = ev 0 = 0);
  cochains EvChart[I,Bad]: Pointwise maps (evc = ev, lowc j = low j,
    pointwise, same support list and chart conditions); evc-add, -zero,
    -sub, -sm;  evc-low : evc x = sum_j a_j evc (low_j x) in the ACTUAL
    A-chart module (pointwise by low-eq; ChartSums.val-sum);
    wit k x : Wit k (evc x) in that chart module, for finitely supported
    x with every coefficient of degree k (induction on k; the cochains
    low_j x keep chart, support and projective degree); witZ.
  No choice: the decomposition x = sum_j var_j low_j x is canonical.
  evT (evaluated term lists), hom-evT, ev-mulP, ev-d0.


6. REGRESSIONS (WeightedRegression4)
------------------------------------
Over any commutative set-ring A, D_2 = A[U][V] from the tower (Uv = U_1,
Vv = U_2):
  part2 : pr 2 (U^2 + UV + V^3) = U^2 + UV ;  part3 : pr 3 (..) = V^3.
  Mono: a concrete cochain c in C^1(-1): U^2 at edge e01, exponent
    (-1,0,0,0), 0 elsewhere (support [m0], chart conditions proved; hc:
    coefficient degree 2).  q = 1 + U:
    scal3 : Pr 3 (q c) = U c         (pr (3-2) q = pr 1 q = U)
    scal1 : Pr 1 (q c) = 0           (requested degree 1-2 = -1 < 0)
Over a CFN A (Dep[K0,cfnA]), the weighted theorem through
CoherentDependence4 (no hand-written syzygy data):
  dep1 : g = (U X_0^3, V X_1^3), d = (3,3), f = (1,1), t = 2;
  dep2 : g = ((U + V) X_0^3), d = (3), f = (1)   (non-monomial coefficient);
  dep0 : t = 0, D = A, g = (X_0^3, X_1^3), f = (0,0);
  t0-neg, t0-one : in D_0 = A, pr (-1) a = 0 and pr 1 a = 0;
  Empty0.empty-case : for N = 0, rs = [] : c_0 = delta v + sum_j g_j a'_j,
    degree-one : v of coefficient degree 1.
Over Z (OverZ; ZRing, ZCFN; a_1 = 2, a_2 = 3, I = (2,3)):
  evU, evV ; ev-UU-UV : ev (U^2 + UV) = 10 ; ev-VVV : ev (V^3) = 27
    (ring-map laws, then computation in Z);
  w10 : Wit 2 (ev (U^2 + UV)),  w10' : Wit 2 10 ;
  w27 : Wit 3 (ev V^3),         w27' : Wit 3 27   (I-power witnesses);
  DZ : the dependence instances over Z[U,V];
  evaluated1 : the evaluated weighted theorem for dep1's input over Z.
No noetherian search result N is predicted; the exported identity,
homogeneity and witnesses are checked.
Mutation tests (restored afterwards): part2 with U^2 + V^3 fails; scal1
with value U c (a k+e reading) fails; projL with the tail length in place
of the fixed N makes sum-proj and hom-projL fail.


7. VALIDATION
-------------
  timeout 55 ./segc sag/zmt-weighted4 changed / all
      109 modules, 0 failed, OK (2.0 s warm server; new files <= 0.14 s each)
  cd sag/zmt-weighted4 ; timeout 55 $(cabal list-bin exe:seg) All.seg
      All.seg: 6633 declarations, 0 failed, 2.69 s, OK
      (5992 = the reused tree of sag/zmt-syzygies4; 641 new)
  New declarations per file: CoefficientParts 89, CoefficientPolynomial
      115, CoefficientCech4 54, BihomogeneousAction4 51, WeightedDependence4
      76, FiniteIdealPowers 23, CoefficientEvaluation4 117,
      WeightedRegression4 116.
  ... All.seg --opened : every new declaration <= 0.06 s, at most 36
      definitions opened (WeightedRegression4.OverZ.ev-UU-UV; the largest
      in a theorem file: CoefficientEvaluation4..ev-A 31).
  ... All.seg --opens zmt-weighted4.opens
      58 central declarations: "nothing else opened" for each (see the
      file header for the carriers and the quotient-ring aliases).
  Baseline unchanged, rechecked fresh:
      sag/zmt-syzygies4/All.seg : 5992 declarations, 0 failed, 2.30 s


8. REMAINING OBLIGATIONS AND SCOPE
----------------------------------
Within this milestone none of the requested constructions is assumed.
Limits, stated honestly:
  * The degree of r_i is stated as the integer N - i (lowerZ (cdeg N) i);
    that it is >= 1 for i < N is not stated as a separate lemma.
  * The finite expression of a homogeneous element is the nested form
    Expr k (sums over j of var j times expressions of degree k-1, ending
    in constants); a flat list of exponent vectors of length t and a ring
    equivalence D_t ~ (exponent-vector polynomials) are not formalised.
  * Ideal powers are by the recursive finite-list definition (Pow, with
    explicit Wit); the conversion to finite monomial combinations
    a^w x_w is not stated.
  * GradingStep lemmas and the D_2 regressions open the operation aliases
    of the quotient ring PolynomialRing.Extension (as in sag/zmt-syzygies4);
    harmless in time (<= 0.06 s).
  * The evaluated identity is stated in the families of
    CoherentDependence4.Over[K0,A,setA,cfnA] (so the evaluated statement
    takes cfnA, which the families themselves do not use).
  * .opens covers 58 of the 641 new declarations.
OUT OF SCOPE (not proved here): full ZMT; the Rees presentation and the
comparison making the evaluated terms ev(g_j) ev(a'_j) vanish (they remain
in the equation); finite-fibre section construction; arbitrary projective
dimension (four coordinates only); a second homogeneous-syzygy
construction or a graded noetherian induction (not needed: the weighted
theorem is a projection of (U)).
