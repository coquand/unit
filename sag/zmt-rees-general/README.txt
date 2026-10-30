zmt-rees-general: constructed generic Rees comparison and correction
==================================================================

Scope
-----
Every polynomial-ring, exchange, finite-kernel-list, chart membership and
homogeneous localized-lift construction is parametric in the finite number
nvar of homogeneous coordinates. The finite correction uses the checked
generic weighted dependence theorem, hence nvar = extra + 3. Charts are the
recursive bitsets GenericCube.Sub nvar, and all actual cochains are
GenericCech.Cochains with the structural newest-vertex-first differential.
There are no new axioms, infinite choices, resizing or flatness assumptions.
Existing standard All.seg univalence/replacement/surjection parameters are
unchanged. All imported files are relative links. No earlier/shared source,
checker or git file was edited by this track.

Final public theorem
--------------------
GenericReesFromSections.Over[K0,A,setA,cfnA,extra,t,b,s,p,e,hp]
 .Sections[z,w,wit,remainder,compatibility].correction

A is an arbitrary CFN set-ring; b is the finite ideal-generator tuple;
p is an ORIGINAL finite homogeneous polynomial list with degrees e. Here
hp is CechPolynomialAction.Hom(pos(e q))(p q), i.e. each term has that degree.
GenericReesTermHomogeneity.Over[A,setA,n].hom converts the natural convention
ShiftedMatrixAction.HomShift zero e p to this integer convention.

The section inputs are actual A-valued GenericCech cochains of twist -1:
 z_n has subset-cardinality 1, w_n subset-cardinality 2;
 wit_n explicitly witnesses w_n in I^(n+1) C^1(-1);
 remainder_n explicitly witnesses d z_n - w_n in the image of ORIGINAL P;
 compatibility_n merely witnesses z_n-z_0 in I C^0(-1) + ORIGINAL P C^0.

The conclusion is merely zz such that d zz is in ORIGINAL P C^1(-1), and
zz-z_0 is in the image I C^0(-1) modulo ORIGINAL P. In the declaration:
 Corrected = (zz:Q0.Target.M) *
   (Q1.InJ (R.d zz) * Q0.IJ 1 (Q0.ML.msub zz (z zero))).
The theorem assumes no KG, resolution, local membership, syzygy generation,
choice of a sequence lift, or cancellation of evaluated KG terms.

Constructed proof components
---------------------------
1. GenericReesRings: S=A[X_0,...,X_(nvar-1)], R=S[U_0,...,U_(t-1)].
   Reuses ReesGenerators4/ReesKernel4/ReesComponents4/ReesFiniteList4: despite
   their names these are already dimension-independent graded-ring proofs.
   CFN gives an ordinary finite elimination generating list; decomposition
   in each grading produces one finite bihomogeneous KG list.
2. GenericPolynomialNaturality and GenericReesExchange: constructed maps
   between R and (A[U])[X], their inverse equations, coefficient evaluation
   and characteristic variable equations. No additional equivalence axioms.
3. GenericReesRepresentatives: merely choose finite term-list representatives
   of the actual bihomogeneous KG. Simultaneous coefficient/projective
   homogeneity is proved, not assumed. GenericReesList.constructed supplies
   all representatives, original-P certificates and homogeneous factor
   representatives under one truncation, called Data.
4. GenericReesPolynomialHom and GenericReesPolynomialMembership: exchange
   a coefficient-homogeneous polynomial back to R, apply the constructed
   elimination ideal, then map explicit finite combination witnesses
   forward. Repetitions are collected into a fixed-tuple ideal witness.
5. GenericLocalizedReesMembership.Chart: clear ONE chart-supported common
   denominator for input AND every original-P multiplier. The cleared
   evaluation belongs to the actual polynomial ideal, so step 4 applies.
6. GenericLocalizedReesLift.Fixed.Chart: project ideal coefficients to
   projective degree k+|L|-d_j, then translate back by L. Exact action,
   projective degree, finite support and the original chart support are
   proved for every integer k and every bitset, not just maximal charts.
7. GenericReesCochainMembership: finite bitset choice, finite support unions
   and a cardinality cut assemble these local lifts into actual generic
   shifted cochains. All choices remain under the result truncation.
8. GenericReesPowerLift.Chart.lift: a FUNCTION of an explicit I^k witness.
   Replace b_j by U_j recursively. The result has coefficient degree k,
   the SAME chart condition, and exact evaluation equal to the input.
9. GenericReesFactor: evaluated KG action factors through ORIGINAL P action
   on actual generic cochains, from explicit certificates, in every twist
   and cardinality. GenericReesChartLaws proves original-J images are
   preserved by the structural differential.
10. GenericReesCorrection reuses EvaluatedWeightedDependence unchanged.
    Construct zz=z_N-sum(ev(r_i) z_i)-ev(v), kill original KG terms by step 9,
    and use proved positivity of N-i and the explicit ideal-power witnesses
    for zz-z_0. GenericReesFromSections constructs c_n using step 8, proves
    evaluated d c_n lies in J using d^2=0, supplies step 7 KG lifts, and
    eliminates the entire Data truncation into the final correction.

Reusable interfaces
-------------------
ImageQuotient.Over[A,t,b,Source,Target,action:Lin] has
 JW x = (y:Source.M)*Id Target.M x(action.f y);
 InJ x = Trunc(JW x), Cong x y = InJ(x-y);
 IJW k x = (x')*(FiniteIdealPowers.Wit k x' * JW(x-x'));
 IJ k x = Trunc(IJW k x).
It proves the image submodule/congruence laws and the ideal-power image
closure used by correction. Native singleton charts can instantiate this
same API; it has no dependency on native localization sources.
GenericReesChart.Over[...].At[k,r] supplies actual GenericCech Target,
shifted source family, original-P action, and Q=ImageQuotient.
GenericReesChartLaws.Diff[k,r].witness/membership transport J along d.
GenericReesFromSections.Over.R.CJ0/R.CJ1 are the rank-1/rank-2 Q modules.

PolynomialCoefficientNaturality, LaurentCoefficientNaturality and
GenericCoefficientPolynomialHom prove coefficient-map/zero-extension and
coefficient-homogeneity statements separately. GenericPolynomialScalar
identifies termwise coefficient scaling with actual tower scalar product.

Regression
----------
GenericReesRegression constructs U_0 X_4 over five coordinates with b_0=1
and original equation P=X_4. The evaluated X_4 coefficient is exactly 1;
OverZ.coefficient-one specializes this to the integer 1. Thus the tested
input/generator are nonzero over Z. SelectedMembership obtains membership
in the CONSTRUCTED KG ideal. chart-lift obtains actual fixed-KG homogeneous
localized lift coordinates for EVERY bitset, choosing only the finite
supports and constructed KG under truncation. The support is computed from
the actual input/multiplier polynomials, not supplied as a hypothesis.
The regression input itself is polynomial; arbitrary nontrivial negative
denominator support is covered by the proved chart theorem, not by a
separate concrete negative-exponent test here.
Two deliberate mutations were rejected and restored: replacing the
coefficient-one conclusion by zero, and assigning U_0 X_4 coefficient
degree zero rather than one.

Validation
----------
23 owned .seg sources, 1121 new declarations; All.seg and .opens are
additional orchestration/audit files.
Fresh built checker: All.seg 11494 declarations, 0 failed.
./segc sag/zmt-rees-general all: 206 modules, 0 failed (see VALIDATION.txt).
Full --opened audit includes every owned declaration: at most 51 definitions
opened, at most 0.39 seconds; largest is the evaluated-action comparison.
Full --opens zmt-rees-general.opens: all 1121 report nothing else opened.
The spec lists allowed definition names once, without multiplicity suffixes.
All checker calls were bounded to 55 seconds. No source was left mutated.

Limits
------
This track proves Rees comparison/correction, not the finite-fibre section
construction, final affine extraction, stable finite-module determinant,
arbitrary-base descent or full ZMT. Those are independent integration
tracks. The final theorem starts at three homogeneous coordinates; smaller
arities require the established padding route or a separate short proof.
We do not remove zero KG columns or optimize degree bounds. We do not
assert polynomial-linearity of selected Cech contractions. We do not
construct a second redundant ring-equivalence package for term lists.
