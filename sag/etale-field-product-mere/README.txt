Constructive etale-to-standard work, 7 November 2026
==================================================

The constructive arbitrary-base theorem is now implemented and checked:
 assembly/LocallyMonicStandardEtale.Over[R,setR,E].theorem fp formal
 : || PrimalityCertifiedCover.Over[E.ring,MonicChart].Cover ||.
Its inputs are only finite presentation and formal etaleness (besides the
set-ring/algebra data). Its output contains finitely many elements h_i,
coefficients c_i with sum h_i*c_i=1, and actual monic standard localisation
certificates for E[1/h_i]. No Fields, CFN, flatness, nonzero-base, decidable
equality, prime-existence, or classical-choice premise remains.
M0--M5 are assembled. No new axiom or checker change was introduced.
The inherited Theory parameters remain univ/images/surjections.

1. Product to component (M0)

ProductComponent.Over[k,setk].Select[S,q,q-add,Bot,q-proper,decide]
 .Given[p].theorem : || Bot + Selected ||

Inputs beyond the actual ProductPresentation p:
 q-add : (a b : S.ring.R) -> q a -> q b -> q (S.ring.add a b)
 q-proper : q S.ring.o -> Bot
 decide : (a : S.ring.R) -> || q a + (q a -> Bot) ||

No primality, multiplication closure, nonzero base, or Bot-proposition
assumption is used. The version .theorem accepts a merely given product.

A Component records a monic coefficient list, the derivative inverse
in its actual quotient Q, and an AlgebraCorner.Retract[S,Q]. That
retract has an algebra projection, an additive/multiplicative section,
projection(section a)=a, and section(b*projection a)=section(b)*a.
Its support is section(1), proved idempotent. ProductComponent.At gives
the generator, monic equation, derivative inverse, and polynomial
representatives of EVERY ambient element on the support.

Family gives the finite family indexed by Leaves of the product tree.
Family.Given[p].sum-one proves that its supports sum to 1.
Select.Given[p].all-in proves Bot when every support lies in q.
The selection recursion uses the same binary support-sum identity.
Zero leaves remain present; no minimality or irreducibility is claimed.

2. Corrected local interface (M0, with M4)

LocalisedZMT no longer takes flatness. Its field boundary is now:

 At[c].Refined : U l = Plus Bot Cert.MF.ChartData
 field : (c : Z.Z.Conclusion) -> Tr.Trunc[At[c].Refined].carrier

FieldCase[field,smooth].theorem returns || Bot + Certified ||.
The old Generator at the original s is only the stronger sufficient
premise of Unrefined. It is not the corrected Fields requirement.

local/SelectedMonicLocal accepts the weak/relative local hypotheses,
the original finite ZMT data and s-out, and a selected multiplier e,
generator x, relative outside witness, and the finite Piece equations.
It proves the localisation law at s'=s*e, converts every exponent N to
N+1, constructs Factor at s', and returns the original ChartData.
No idempotence of the lift e in B is assumed. No assertion that s'=1
modulo mE is made or needed. local/RefinedZMT instantiates this at the
actual ZMT output and maps its result into At[c].Refined.

residual/ZMTResidualComponent now lifts ProductComponent into this Piece
and supplies SelectedData at the actual ZMT output. See section 5.

MonicFiniteLocal.SmoothField and LocalDescent.SmoothChart call
ShortLocalEtale.theorem with formal smoothness. Their flat wrappers
remain, using the proved FlatUnramifiedEtale implication. Descent and
the corrected LocalisedZMT/HitOrSplitLocal route carry smoothness from
the original algebra, without a hidden flatness input.

The older conditional HitOrSplitLocal wrapper has this premise:

 Fields : U l = (s : List E.R) (proper : Not (P.Mem s E.o))
  (dec : HS.Decision s) -> At[s,proper,dec].FieldCases

where FieldCases is the refined field boundary above. Given[field]
.theorem smooth K0 cfn still needs Fields and CFN. Its flat-theorem is
a separate specialization. residual/ConstructiveEtaleCover discharges
Fields; assembly/LocallyMonicStandardEtale also removes CFN. The older
conditional wrappers remain available unchanged.

3. Degeneracy and weak-field structure (M1, partial M2)

ZeroProduct.Over[k,setk].At[S,one-zero].theorem gives an actual
ProductPresentation when 1=0 in S. BaseZero[one-zero].theorem S does
the same when 1=0 in k. The polynomial is 1. Both maps and both
inverse equations are proved; its derivative is a unit in the zero
quotient. No global decision whether 1=0 is made.

GaussianQuotient.Operations contains the decision-free pivot proof.
Its exact Over endpoint retains actual normal forms. MereGaussian
recurses under truncation using FieldFlat.Mere's finite row scan:

 weak : (a : k.R) -> || (a=0) + unit(a) ||
 normal-form : (n m : Nat) (v : Fin m -> Vec n) -> || NormalForm[n,m,v] ||

The shared GaussianModuleQuotient now packages a supplied normal form.
GaussianAlgebraBasis.FromNormalForm and FiniteFreeQuotientBasis.Data
expose the decision-free basis construction; exact wrappers remain.
FinitePresentedFieldBasis.theorem consumes mere normal forms, while
exact-theorem retains exact decisions. Existing callers were updated.

MereFieldStructure.Over[k,setk,weak].At[S,fp,unique].theorem constructs
the existing UnramifiedFieldStructure.Data[k,setk,S].Structure:
dimension, actual finite basis, trace duality and perfect trace.
It assumes neither nonzeroness nor a basis, trace, prime or product.
Its finite span comes from UnramifiedFieldFiniteGeneral. The ordinary
field product and selected-field theorems still check with these changes.

4. Weak minimal polynomials, large branch and coefficient models

The bounded power-span search is now proved in MereMinimalPolynomial.
PowerSpan and MinimalPolynomial expose their decision-free definitions;
the original exact search is retained under Exact[field]. The weak
search uses MereLinearSeparation: either actual span coefficients or a
normalized functional killing the span. It scans only below the supplied
monic annihilator degree, then uses that relation at the final degree.
No nonzero assumption is needed at termination. In the separating case,
a unit leading coefficient would give a span witness; overlap proves
1=0 and hence the leading coefficient zero. Minimality and the existing
division theorem apply to the same Minimal record.

MinimalPolynomialInjection now needs no field parameter. Its quotient
embedding and both monogenic inverse maps are unchanged. Exact regularity
is a separate endpoint taking exact zero-or-unit decisions.
ReducedIntegralRegular.Mere strips coefficients under truncation;
FiniteReducedRegular.theorem now takes weak decisions and exact-theorem
retains the previous proof. MereGeneratedMonogenic constructs a separable
monic presentation from a generator, finite basis, reducedness and
nondegenerate trace over a weak field.

MerePowerFunctional obtains the normalized top-power functional from
minimality, returning the zero functional with target 1 when overlap
proves 1=0. MereSeparatorDerivative eliminates that mere functional into
the proposition of derivative units. MereSeparatorMonogenic constructs
an actual separable monic presentation from a tensor separator.

PolynomialRootBound.Units now states the synthetic-division theorem using
pairwise UNIT DIFFERENCES. Its former field theorem specializes it.
MerePolynomialSelection scans determinant values; all values zero imply
1=0 by determinant regularity and are a success case. Consequently
MereLargeFieldMonogenic proves the large branch from a sufficiently long
unit-separated family. It needs no supplied generator, exact decision,
nonzero base, or finite coefficient subfield.

MereSeparatedLookup and MereFiniteClosure construct the bounded closure
dichotomy with weak decisions. The closed outcome includes actual finite
operation tables and zero-or-inverse witnesses. FiniteTableReflection
compares only finite indices: equal values at unequal indices give 1=0.
FiniteClosedField checks every finite ring law and field law this way.
MereCoefficientDichotomy therefore returns merely one of:
 - 1=0 in k;
 - a sufficiently long unit-separated scalar family;
 - an actual nonzero finite field model mapping to k, with explicit
   preimages of all requested coefficients.
The model map is NOT asserted injective. No decision whether k is zero
is made. All exact ordinary-field proofs remain in the import tree.

The small branch and full weak-field product theorem are now proved.
MereCoordinateEquality and MereFiniteDedup retain finite representatives
and origins. Equality of retained images implies equal indices OR base
collapse; it never supplies injectivity. FiniteReducedTable checks the
finite ring laws and reducedness. MereFiniteImage gives an actual finite
reduced model mapping to the ambient algebra, and checks the coefficient
map separately. MereModelProduct refines this exact finite model into
finite field corners, transports polynomial representatives and all
idempotents (including zero images), and uses weak corner monogenicity.
MereSmallFieldProduct applies this to the finite iterated monic algebra.
MereFiniteEtaleProduct joins it to the large and collapse branches.

The public weak-field endpoint is:
 MereUnramifiedFieldProduct.Over[k,setk,weak].At[S,fp,unique].theorem
 : || ProductPresentation.Over[k,setk].At[S] ||.
Only weak : (a:k) -> ||(a=0)+unit(a)|| is required, and formal
unramifiedness suffices. MereProductRegression includes F2^3, zero targets,
zero bases, and the explicitly noninjective coefficient map F2 -> 0.
The exact-field proofs remain, with decision-free corner/span interfaces
and wrappers preserving their former computations.

5. Completed assembly (M3 and M5)

residual/ZMTResidualComponent uses E_M/mE_M directly. At the ORIGINAL
ZMT output, s=1 in that quotient. The actual finite subalgebra B therefore
maps merely onto it: s^N*z=j(b) becomes z=j(b). The relative ideal descends
through mE_M by RelativeQuotientIdeal, and the weak product theorem selects
a component. ComponentEquationLift lifts its finite coefficient lists,
generator, support and inverse. IdealPowerClearing returns explicit
positive powers of the original s for every equation. SelectedMonicLocal
then refines s to s*eps, retaining these powers. B/mB is never assumed to
embed. This route bypasses the explicit quasiinverse for (B/mB)[1/s]; it
proves the local boundary using the original s=1 identity instead. The
existing OriginalSQuasiInverse and its proofs remain in the tree.

residual/ConstructiveEtaleCover discharges Fields at every hit-or-split
node. This intermediate theorem still takes CFN of E; it is not the final
arbitrary-base endpoint.

assembly/LocallyMonicStandardEtale removes that hypothesis constructively:
 - JacobianOpenReduction gives E as a principal idempotent open of an
   actual square Jacobian algebra.
 - CoefficientSquareData records coefficient occurrences of its system
   and one expression for the open element, over Z[C_1,...,C_m].
 - ScalarJacobian and JacobianScalarExtension construct the maps and
   prove the determinant and generator comparisons.
 - The generic square Jacobian localisation is formally etale by the
   existing Jacobian lifting proof. Its extra principal open is formally
   etale by FormalEtaleLocalization. The extra element need NOT remain
   idempotent in the coefficient model: localisation at any element works.
 - CFNPresentedAlgebra proves CFN from the actual finite presentation,
   using polynomial extensions, principal quotients, and the proved
   presentation isomorphism. It assumes CFN only of the coefficient base.
 - The unconditional local input gives the finite CFN cover. Its actual
   monic chart algebras, maps and unit equation are specialised by
   StandardScalarValues, ScalarExtensionProperties,
   LocalizationScalarExtension, and MonicCoverScalarExtension.

Absorbing the idempotent open into the generic model BEFORE taking its
cover replaces the handoff's proposed final restriction step. No formal
smoothness certificate is silently descended. The endpoint has no remaining
mathematical hypothesis beyond fp and formal etaleness. Standard chart
certificates carry the full mapping-out equivalence, not merely roots.

6. Validation

New proofs live here and in local/, residual/, and assembly/, with relative dependency links and
separate All.seg files. Shared changes extract decision-free Gaussian, polynomial, functional,
regularity and finite-scan interfaces and retain the exact endpoints.
Their callers and the local/smooth adapters were updated.
No gerbe/H2 source was edited.

Initial M0/structure --opened checks (before the continuation):
 main All.seg: 19,103 declarations, 0 failed (10.24 s).
 local/All.seg: 31,203 declarations, 0 failed (25.15 s).
Both retain only the inherited Theory parameters univ/images/surjections.
The matching opening inventories are product-mere.opens and
local/component-local.opens; declarations were inspected by mathematical
construction group. The derivative comparison was split into named
source-slope and source-inverse steps before recording the inventory.

Regressions include the existing computed product of F2^3, a zero
factor, zero target, zero base with polynomial 1, all supports in q,
weak Gaussian elimination and weak structure for both F2 and the zero
base. Existing large/small ordinary-field and Z/4 basis regressions
remain in the checked dependency tree. These check terms, not extracted
normal forms of the entire truncated product.

Four isolated mutations were rejected: omit the derivative inverse,
drop the complementary support, omit refinement of s, and drop an
inverse-map equation. See mutation-results.txt. Shared sources were
not mutated for these tests.

Recheck from unit/ (each command bounded below 60 seconds):
 timeout 55 ./segc sag/etale-field-product-mere all
 timeout 55 ./segc sag/etale-field-product-mere/local all
 timeout 55 ./segc sag/etale-field-product-mere/residual all
 timeout 55 ./segc sag/etale-field-product-mere/assembly all
For opening audits, use the built seg executable with --opens and the
corresponding All.seg and inventory. Fresh downstream checks are listed
in validation.txt.

Continuation validation:
 The expanded main tree checks 19,654 declarations, 0 failed.
 The ordinary exact-field product tree also passes (18,943 declarations).
 weak-field.opens records 1,816 reviewed declarations from new and
 affected shared modules; its --opens audit reports no extra openings.
 Additional regressions cover weak bounded minimality, division and
 monogenic inverse maps for F2 x F2; zero-base positive-branch overlap;
 the weak large branch for F2 and a zero base; an explicit two-element
 coefficient-field table and a degenerate singleton table. Four new
 isolated proof mutations are rejected. See validation.txt and
 mutation-results.txt. No checker changes or axioms were added.

Completion validation is recorded at the end of validation.txt. New
opening inventories are small-branch.opens, residual/residual.opens, and
assembly/assembly.opens. These include every new declaration and the
affected shared interfaces. MonicCoverRegression exercises the final
endpoint on a nonreduced Z/4 base, redundant equations, nilpotent
localisation, a zero base, and an arbitrary-base identity algebra.
