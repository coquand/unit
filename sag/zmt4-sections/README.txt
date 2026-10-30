Constructed finite-fibre sections for ZMT4
========================================

1. Completed result

FiniteFibreSections4.Over[A,setA,D0] constructs the finite-fibre input (D)
from residual data D0 for THREE affine generators over ANY commutative
set-ring A. No field, CFN, properness, flatness or section hypothesis is
needed here. The sequence consists of explicit finite formulas in n;
there is no sequence of choices.

It exports:
  ST.P/ST.e/ST.hp/ST.deh-P -- constructed homogeneous residual generators
  z n : CJ0.E.El
  w n : CJ1.E.El
  wit n : CJ1.FC.Wit (suc (PolynomialRing4Bridge.toB n)) (w n)
  remainder n : CJ1.JW (CJ1.ML.msub (d.f (z n)) (w n))
  compatibility n : CJ0.IJ 1 (CJ0.ML.msub (z n) (z zero))
  hz n m : coefficient of z_n on chart Z is EXACTLY Z^(-1), for all n
  hz0 m : the same statement for z_0, in the correction interface.

CJ0 and CJ1 are the actual ReesChart4 modules on Pt and Ed at twist -1,
using the new ST.P/ST.e/ST.hp. d is the existing Cech4 differential.
JW and Wit retain explicit J coefficients and ideal-power witness trees.
Compatibility[n].witness even gives the untruncated IJW; truncation is
introduced only to match the unchanged ReesCorrection4 input interface.

All parts needed for the section conclusion are constructed. The generic
ring/chart algebra helpers have parameters, but the final theorem has
ONLY A, setA and the original residual data as parameters.

The root integration composes these outputs with the constructed Rees
lifts, correction and extraction in zmt4-completion/FinalZMT4.seg. That
separate integration proves the ZMT certificate and arbitrary-base export;
this directory establishes the finite-fibre section portion.

2. Ownership and dependencies

There are fourteen new local .seg files, 539 declarations. No shared
library, earlier development, checker, .git or other agent's source was
modified. Older files are relative links. Nothing is committed. All.seg
inherits exactly the earlier foundational parameters; no new axioms,
infinite choice or resizing principle is introduced.

Two parallel foundations are imported unchanged:
  zmt4-laurent-ring: 529 declarations constructing native chart Laurent
    rings, coefficient extensionality, support, degree cuts, polynomial
    multiplication, restrictions and explicit coordinate inverses.
  zmt4-section-components: 65 declarations assembling the explicit point
    sections and proving their overlap/compatibility coefficient equations.

The root supplied GeometricSectionsAlgebra, SectionsErrorWitness,
SectionExpression4, FiniteSingleCoefficient, ChartFamilyAssembly4,
ProductIdealWitnesses, IdealPowerWitnessTransport and ChartErrorAssembly4.
The Rees-lift agent supplied ChartErrorWitness4. Their files are linked
unchanged. All these helpers have their own proofs, not extra axioms.

3. Simplified construction

Let d_k be the degree of the monic residual polynomial. Instead of
homogenising an already expanded residual expression, keep its monic
part visible. Define a homogeneous monic expression M_k of degree d_k
by the recursive reversed lower polynomial. Choose
  delta_k = 1 + sum_j bndT(tl H_kj),
  e_k = d_k + delta_k,
and use the homogeneous equations
  P_k = Z^delta_k M_k - sum_j b_j hom_(e_k)(tl H_kj).
They dehomogenise to the ORIGINAL residual equations in the ORIGINAL
residual algebra E. No equality to the earlier ZMT4Setup.P is asserted
or needed: the choice of homogeneous generators is free, and the root
extraction/assembly was parameterised by P/e/hp/deh-P.

On chart X_k, put v_k=X_k^(-1), u_k=Z v_k. The monic recurrence proves
  v_k^d_k M_k = H_k = 1+u_k Q_k,
  G_k=u_k^delta_k H_k
     = sum_j b_j (v_k^e_k h_kj) + v_k^e_k P_k.
These are exact identities in the CONSTRUCTED native chart ring.

For p=n+1, recursively construct Q_(k,p) with H_k^p=1+u_k Q_(k,p).
Choose the common, deliberately generous exponent
  M = sum_k delta_k*(p+1), L=M+1.
It is at least delta_k*p and at least delta_k for each k, with explicit
complementary-exponent witnesses. Define
  a_k=sum_(i<L)(-u_k Q_(k,p))^i,
  b_k=(-Q_(k,p))^L,
  t_k=b_k u_k^M,
  section_k=t_k v_k.
The checked geometric-series identity gives
  1-Z section_k = a_k H_k^p.
On the chart Z the section is always Z^(-1).

For affine overlaps use the exact identity
  z-w = z(1-Zw)-w(1-Zz).
Each cross term contains u_k^M H_l^p. Since
u_k=(X_l/X_k)u_l, the explicit bound rewrites it as
  (X_l/X_k)^M u_l^(M-delta_l*p) G_l^p.
G_l^p has an explicit I^p+J witness by the ideal-power and telescoping
recursions. No idempotence or comparison-of-idempotents lemma is used.
On a Z/affine overlap, the same Cross lemma uses u=1 and
ratio=X_k/Z; the complementary Z-section error is exactly zero.

For section_n-section_0 on one affine chart, use Cross with p=1 on BOTH
terms. Rewrite a_n H^(n+1)=(a_n H^n)H. The common bound is at least
delta_k, including for the n=0 section; no comparison of M_0 with
delta_k*(n+1) is required.

Native chart elements have finite coefficients and chart support by
construction. Project the resulting exact ring equations to degree -1.
The degree projection is A-linear and commutes with each homogeneous
P_q after shifting its multiplier degree. Thus arbitrary intermediate
witness coefficients need not be homogeneous. Realize the explicit
ideal/J witnesses in singleton actual chart modules, then use the finite
Pt/Ed assembly maps. Restriction preserves coefficients and the explicit
section expressions, so the assembled edge errors are precisely d z_n.

4. Local files and proof correspondence

MonicFriendlySetup (60)
  xp and its degree/monomial laws; lower, hom-lower, deh-lower; monic,
  hom-monic and deh-monic; explicit bounds; homogeneous H terms; P/e/hp
  and deh-P in the original residual algebra. The degree-zero monic case
  is included by the base branch of the same recurrence.
SectionsPowerAlgebra (17)
  Base.Nat powers and addition/product laws. PowersOfOne.quotient/factor
  constructs H^p=1+uQ_p recursively.
SectionsIdealPowers (34)
  Explicit ideal witness scale/add/neg/sub; Power.witness for a power of
  sum b_j x_j; explicit J coefficient calculus; PowerDifference.coeff/
  equation proves x^p-y^p is in J by a telescoping recursion.
SectionsDenominatorAlgebra (32)
  Natural product times and finite common bounds. Clear.equation gives
  the exact overlap conversion to a multiple of G^p.
PolynomialRead4 (32)
  The ring map from the constructed polynomial ring reads term lists;
  operation comparisons and scalar/monomial formulas use the named
  existing PolynomialRing4Bridge lemmas.
NormalizedMonicAlgebra (19)
  A unit-power identity normalises the monic homogeneous expression;
  lower-factor and monic-factor prove it is 1+uQ, with explicit Q.
MonicChartRelation (52)
  Compare polynomial reading with that recurrence, normalise P and its
  error sum, and derive G=sum b_j h_j+v^e P_q exactly.
ChartUnitAlgebra (11)
  Unit/ratio, constant-power and error-one identities used on overlaps.
NativeSectionData4 (69)
  Instantiate the preceding algebra in the native chart rings; provide
  each G^p witness, explicit section formula, common exponent and actual
  coefficient-preserving restriction of the formula to overlaps.
NativeSectionErrors4 (68)
  Construct affine Cross/Overlap, ZAffine overlap, and same-chart
  Compatibility native I^p+J witnesses.
SectionErrorRealization4 (37)
  Apply the proved singleton realization and global chart assembly to
  a native error family, preserving actual Wit and explicit J coefficients.
FiniteFibreSections4 (35)
  Final actual sequence, explicit ideal-power errors, boundary remainder,
  compatibility and exact Z normalisation from residual data alone.
SectionsRegressionData4 (33), SectionsRegression4 (40)
  Concrete residual inputs and actual front-half witness tests below.

5. Regressions, mutation checks and validation

The front-half regression instances construct the final sections, ideal
witnesses, J remainders and compatibility without correction parameters:
  - finite point over any set-ring: P=T, H=0, t=0;
  - zero fibre over any set-ring: P=1 (degree zero), H=0, t=0;
  - nonreduced base Z/4Z: P=T^2, b=(2), H=1 for each residual generator.
The last instance additionally proves that the ACTUAL second-order error
w_1 is zero, by following its explicit ideal witness tree and using
2*2=0. Thus the empty-ideal and degree-zero cases are not only comments.

Two isolated temporary-copy mutations were rejected:
  - changing the residual error sign in P breaks hp/deh-P/read-P;
  - omitting u in the reversed lower quotient breaks lower-factor and
    section-expression naturality.
Live sources were never changed during these tests. The component agent
also rejected reversed overlap and compatibility differences in isolated
copies. The complete unchanged source tree checks afterwards.

Commands from unit:
  timeout 55 ./segc sag/zmt4-sections all
From sag/zmt4-sections, with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt4-sections.opens

Final recorded results:
  segc: 210 modules, 0 failed.
  Fresh All.seg: 12006 declarations, 0 failed, about 7.2 s.
  Local files: 14; local declarations: 539.
  --opened: every new declaration at most 30 definitions and 0.03 s.
  --opens: all 539 profiles report "nothing else opened".

The profile lists explicitly include structural power, monic, bound and
witness definitions; native ring/carrier aliases; constant inclusions
through the polynomial towers and localisation; and chart/submodule
carrier, operation, degree-projection and assembly aliases. At native
instantiations the checker identifies polynomial and chart scalar maps
through these definitions. Formula coefficients use the same named
PolynomialRead scalar map as the monic relation, reducing the largest
opening count from an intermediate 48 to the final 30. The text does
not claim complete opacity of quotient/localisation operation aliases.

The result is exactly the finite-fibre input needed by the checked Rees
and extraction integration. The final certificate/descent theorem is
exported separately by zmt4-completion; no earlier conditional assembly
file or earlier README was overwritten to relabel it as unconditional.
