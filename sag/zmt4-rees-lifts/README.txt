ZMT4 Rees lifts -- Gate (E)
==========================

1. Status

Gate (E) is constructed and checked. The development lives only in this
new directory: 8 owned source files, 411 declarations. Dependencies are
relative links to existing developments and root's zmt4-completion files.
Nothing is committed. No shared/earlier source, checker or .git file was
edited by this track. No axiom, choice or resizing principle was added.
All.seg retains only the existing univalence/replacement/surjection inputs.

This is the Rees/cochain lifting gate. The finite-fibre section construction
(D), final correction/extraction integration and the full ZMT statement are
owned by the other tracks; their completion is not asserted here.

2. Final theorem -- EXACT correction interface

ReesCochainLift4.Over[K0,A,setA,cfnA,t,a,s,p,e,hp]
  .List[w,fw].Input[n,c,hc,jy].lift
  : Trunc[CI.Lifted c]

Here A is a CFN commutative set-ring; a:Fin t->A gives I; the ORIGINAL
homogeneous equations p_q have nonnegative X-degrees e_q (hp). They can be
any such list; no equality with the older ZMT4Setup generator list is used.
In particular the new monic-friendly setup may be substituted directly.

w and fw are the exact GenAt list and fixed bounds of the unchanged
ReesCorrection4.List[w,fw]. The fixed list KG is not replaced or enlarged.
CI is exactly that correction list's ED.WD.CI, built by unchanged
CoherentDependence4. n:Base.Nat, c:CI.F1.E0.El=C^1_D(-1), D=A[U_1..U_t],
and hc states that every coefficient of c has U-degree n.

jy states that evaluated delta(c) lies in the ORIGINAL equation ideal on
ACTUAL A-valued C^2(-1) cochains:
  J.InJ (EC.evc (CI.D1.d0.f c)),
where J=ReesChart4.JC[Tri,setTri,-1] and EC evaluates that Tri chart.

The result merely supplies u in product_j C^2_D(-1-dX_j) and the exact
cochain identity
                delta(c) = sum_j gD_j u_j.
It is the precise CoherentDependence4.Lifted c consumed by correction.
No localised kernel membership, local generation, coefficient vector,
primitive, denominator, chart representative or gluing theorem is a new
hypothesis. All are constructed below. n=0 is included.

3. More general cochain membership theorem

ReesCochainMembership4.Over[...].List[w,fw].Degree[k]
  .Input[n,y,hy,jy].lift

k is ANY integer, y is an actual D-valued Tri cochain of X-degree k,
hy gives coefficient U-degree n, and evaluated y is in original J as an
actual A-cochain. The output merely gives z in the exact KG family of
X-degrees k-dX_j, together with y=KG.A(z). Negative target degrees are
allowed and are handled by homogeneous projections, not excluded.

4. Polynomial input reused from root

ReesPolynomialMembership4.List[w,fw].fixed-membership is the starting
polynomial theorem. It uses the ACTUAL exchange isomorphism
S[U] <-> A[U][X] in ReesExchange4 and the already constructed Rees kernel
elimination theorem. It returns a truncated coefficient vector for the
exact fixed KG list, for a coefficient-U-homogeneous polynomial whose
evaluation is in polynomial J.

This track links root's TowerUniversal, TowerExchange,
PolynomialFourNaturality, GradedHomogeneousMap, ReesExchange4,
ReesPolynomialMembership4 and IdealPowerReesLift4 files unchanged.
Root preserves their public APIs while improving boundary comparisons.
The final E theorem does not need an ideal-power lift as an input; root's
sequence integration uses IdealPowerReesLift4 to produce its c_n first.

5. Constructed local proof

ChartDenominators4
  Given ANY chart subset E and finite support S, take the coordinatewise
  negative-part bound and mask it: L_i=0 outside E. This is critical for
  unshifting back into the SAME intersection, including proper Tri charts.
  A support entry with a negative outside coordinate need not be admissible:
  its coefficient vanishes by the original chart condition. The proof does
  not falsely assume all members of an oversized support list admissible.

HomogeneousCoefficientRepresentation4
  The existing explicit finite coefficient-function representation selects
  only the given homogeneous U-coefficients and counts exponents once.
  Proves the representative retains coefficient U-degree n, rather than
  assuming a homogeneous representative or projecting without a bridge.

LocalizedReesMembership4
  Clear ONE common chart-supported denominator for the D-valued input AND
  all A-valued original-J multipliers. Construct finite polynomial
  representatives, prove evaluation agrees with the original polynomial
  J combination, then invoke root's fixed-membership. This is actual
  polynomial J membership, not an unjustified inference from membership
  after localising. It works on arbitrary Sub4, not just the fully inverted
  chart.

LocalizedReesLift4
  Eliminate the obtained truncated fixed coefficient vector and choose its
  finitely many term-list representatives under truncation. Their ring
  identity is converted to the exact coefficient action equation.
  Project coefficient j to X-degree k+size(L)-dX_j. Additivity, the graded
  polynomial action and homogeneity of the input reconstruct the cleared
  equation for EVERY integer degree. Unshift by L. Prove explicitly:
    - the exact fixed-KG action equals the original function;
    - the original chart condition, because L is zero outside E;
    - homogeneous X-degree k-dX_j;
    - finite support, by translating each representative's finite support.

TriFiniteChoice4, ReesCochainMembership4
  Choose finite support witnesses of y and the actual original-J
  multipliers, unite them, apply the local construction at all four Tri
  components, and choose those four outputs only under truncation. Unite
  their supports and use the proved degree/chart conditions to construct
  ACTUAL Laurent chart cochains. Their cochain-family equation is proved
  by coefficient extensionality. No quotient/tensor-product identification,
  flatness assumption or global choice is used.

ReesCochainLift4
  Coefficient projection commutes with delta by the unchanged
  CoefficientCech4.Diff.D1-proj, so hc gives the same U-degree for delta(c).
  Apply the general Tri membership theorem to get precisely CI.Lifted c.

6. Regressions

ReesLiftRegression4 checks:
  - the exact c-lift theorem at U-degrees 0 and 3 over arbitrary CFN A and
    arbitrary original homogeneous equations/fixed KG data;
  - a genuinely nonzero proper-chart cochain: with t=0 and J=(1), y is
    X0^-1 on Tri t012 and zero on the other three components. The KG list
    and its bounds are CONSTRUCTED with WC.finite-list; returned KG action
    at that exponent is proved equal to 1. No matrix generation is assumed.
  - a common support containing BOTH (-1,0,0,0) and the forbidden exponent
    (0,0,0,-1), on chart t012. The fourth denominator coordinate is proved
    zero, rather than clearing a variable that is not inverted.
  - the nonzero unit-equation construction over Z, and an empty-equation,
    empty-I Z instance of the general exact lift theorem.

Two mutations were rejected, then restored and rechecked:
  - allowing a denominator exponent outside the chart: gate-add,
    gate-sub and neg-or-out fail;
  - projecting to k+size(L)+dX_j instead of k+size(L)-dX_j:
    projected-equation, polynomial, degree and vanish fail.

7. Commands and validation

From CANONICITY:
  timeout 55 ./unit/segc unit/sag/zmt4-rees-lifts all

From this directory, with SEG the existing built executable reported by
`cabal list-bin exe:seg` in unit:
  timeout 55 "$SEG" All.seg
  timeout 55 "$SEG" All.seg --opened
  timeout 55 "$SEG" All.seg --opens zmt4-rees-lifts.opens

The final fresh/server counts and timings are in VALIDATION.txt.
All 411 owned declarations have explicit opening inventory entries.
The recorded --opened maximum for an owned declaration is 43 distinct
openings and 0.04 s. The inventory is measured, not an independently
minimal whitelist. Quotient/tower aliases, KG record fields, finite sums
and chart constructors are explicitly declared. No checker change was made.

8. Integration and limits

The fixed KG list, original J list and all degrees are retained exactly.
The public theorem is generic in p/e/hp and so accepts the monic-friendly
section setup without transports to the old homogenisation list.

Root's checked ZMT4FromSections now consumes this E theorem, together with
its explicit section data D and ideal-power lifts, to form the sequence and
perform correction/extraction. This directory does not construct those
finite-fibre sections. No assertion of full ZMT follows merely from this
E milestone in isolation.
