Generic weighted dependence and evaluated ideal powers
======================================================

Status: completed, checked, uncommitted. All new proofs are in this directory;
existing developments/checker/shared files are unchanged relative links.
Eight owned source modules, 514 owned declarations. No new axioms or choice.

Main theorem
------------
GenericWeightedDependence.Concrete[K0,A,setA,cfnA,t,extra].W
 .Input[a,d,f,g,hg,hf].Seq[c,hc,lift].dependence

D is the unchanged constructed coefficient tower A[U_1,...,U_t], including
t=0, with its proved grading, evaluation maps and iterated Hilbert CFN.
The number of homogeneous X coordinates is extra+3 (extra : Ring.Nat).
The base A is an arbitrary CFN set-ring, not necessarily a field/domain.
The X and U dimensions are independent.

Ordinary exponents are Fin n -> Base.Nat; Laurent exponents are Fin n -> Int.
GenericCube.Sub n indexes subsets; integer r is SUBSET CARDINALITY, so
ordinary Cech degree q means r=q+1. The newest coordinate inr tt is first
in the orientation, giving d(a,b)=(da,a-db). No fixed N4/E4 model is used
for any new cochain, action, projection, evaluation or theorem.

The input g_i is a finite term list in X, homogeneous of natural X-degree
d_i (standard HomShift zero d_i), with every coefficient homogeneous of
natural U-degree f_i (GenericBihomogeneousAction.CoefHom). The original
c_j are ACTUAL C^1(-1) cochains over D, with coefficient degree j+1.
Only their original mere lifts delta c_j=sum_i g_i u_ji are required.
No homogeneity of the lifting cochains is required; no resolution is an
input and no syzygies are constructed by this development.

The conclusion is merely rs,v,a', N=len(rs), satisfying the actual identity
  c_N - sum_(i<N) r_i c_i = delta v + sum_j g_j a'_j,
where r_i has U-degree N-i, v has degree N+1, and a'_j has degree
N+1-f_j. N=0 is allowed. Negative degrees mean the zero homogeneous part;
no positivity hypothesis is inserted. The list is stored in descending
index order: an entry with tail length i multiplies c_i. Projection uses
the fixed OUTER N throughout, not the current tail length.

Evaluated theorem
-----------------
EvaluatedWeightedDependence.Concrete[K0,A,setA,cfnA,t,extra,b].ED
 .Input[a,d,f,g,hg,hf].Seq[c,hc,lift].evaluated

Here b : Fin t -> A, I=(b_j), ev(U_j)=b_j. The merely produced EvResult is
 (w : WS.WResult) * EvBdry w.
Use WS.WR[w] for rs,N,v,a', hom-r, hom-v, hom-a and the weighted equation.
EvBdry contains:
 - actual A-cochain identity
     ev(c_N)-sum_i ev(r_i) ev(c_i)
       = delta(ev(v))+actionA(evE1(a'));
 - PowL N rs: explicit WitZ(N-i,ev(r_i)) for every list entry;
 - explicit Wit(N+1,ev(v)) in the actual C^0_A(-1) module;
 - explicit WitZ(N+1-f_j,ev(a'_j)) in each actual shifted C^1_A module.
actionA is the explicit finite sum of actions of evT(g_j). Thus the
ORIGINAL evaluated defining-polynomial terms remain visible. Their
factorization/vanishing in an equation ideal is left to Rees comparison.
No CFN assumption on A is needed for the abstract evaluation wrapper;
Concrete takes CFN A to construct CFN D for scalar dependence.

Reusable APIs (all stable)
--------------------------
GenericCoefficientCech.Over[A,t,D,setD,G]
 .ChartPr[Ex,I,Bad]: coefficient projection on any GenericLaurent.Chart;
   .Hom/.proj/.hom-proj/.proj-hom/.proj-add/.proj-sub/.proj-sum,
   .proj-scalar-pos and .proj-iota.
 .CochainPr[n,k,r].P: same construction for actual GenericCech.
 .Diff[n,k,r].equation: projection commutes with actual differential.
GenericBihomogeneousAction.Over[A,t,D,setD,G,n]
 .CoefHom f: per-term coefficient homogeneity; nilTop, cons Hom*rest.
 .Act[ki,ko,r,p,hp,f,hf].equation: Pr_e(p*x)=p*Pr_(e-f)(x).
 .RowPr: coefficient projection on finite source families and their row.
GenericCoefficientEvaluation.Over[A,setA,t,D,setD,G,b,n]
 .evT: plain term-list coefficient evaluation;
 .hom-evT/.shifts-evT preserve X degrees/shift conditions;
 .EvChart[Ex,I,Bad]: .evc/.evc-add/.evc-sub/.evc-sm/.evc-sum,
   canonical .lowc and explicit .wit/.witZ into actual A-chart modules;
 .CochainEv[k,r].E, .Diff[k,r].equation, .Act[ki,ko,r,p,hp].equation.
The evaluation ring map is .ev. GenericLaurent support is preserved by
pointwise zero-preserving maps. Canonical low maps build ideal-power trees
without choosing pointwise witnesses or flattening monomial expressions.

Proof structure
---------------
The unchanged ScalarResolutionDependence theorem supplies the final
ordinary identity. Its nested boundary truncation is eliminated into the
weighted result. Project that identity to coefficient degree N+1; this
requires only additivity, structural differential commutation, and
coefficient-homogeneous polynomial action. No homogeneity of the ordinary
q/h/a witnesses is assumed. The generic syzygies and resolution-to-
certificate arguments are reused unchanged. Evaluation then maps this
actual identity and constructs finite ideal-power witness trees using
the already proved coefficient tower low decomposition.

Regressions
-----------
GenericWeightedRegression constructs an actual five-coordinate C^1(-1)
cochain, supported at subset {newest,next-newest} and exponent
(-1,0,0,0,0), with coefficient U^2+UV. It checks scalar projections at
3-2 and 1-2, actual differential commutation, evaluation and explicit I^2
membership. Over Z at b=(2,3), its evaluated coefficient is 10.
Five-coordinate (U+V)X_newest^3 exercises the generic weighted and evaluated
theorems, including an actual zero sequence with constructed lifts.
Corner cases: empty coefficient-variable block, empty defining rank,
zero polynomial declared degree5, negative multiplier degree, explicit
N=0 projected boundary, and fixed-N indexing for two list entries.
Concrete Corner instances cover 3,4,5 homogeneous coordinates over Z.
Scalar coefficient identities/numerical calculations are reused unchanged
from WeightedRegression4; new actual cochains all use generic exponents.

Mutations of the coefficient projection shift (k+f instead of k-f) and of
fixed-N indexing to current tail length are rejected, then restored.
See VALIDATION.txt and zmt-weighted-general.opens.

Limits
------
The theorem covers n>=3 via n=extra+3; n=0,1,2 projective assertions are
not claimed here. No Rees kernel, equation ideal quotient, section
construction, final ZMT export or arbitrary-base descent is proved here.
Integer exponents N-i are retained; no separate strict-positivity lemma
for list positions is needed. Ideal powers retain their checked recursive
finite-tree representation. No equivalence with flat monomial-combination
representations is added. The .opens inventory lists measured names for
all514 owned declarations; it is not an independent minimal allowlist.
