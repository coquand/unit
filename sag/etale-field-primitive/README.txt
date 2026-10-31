Selected-prime ingredients, minimal polynomials and trace descent
===============================================================

Status: the algebraic ingredients below are checked. The full selected
primitive-element existence theorem is NOT proved. In particular,
SelectedFactorStatement.Result is a target type, not a theorem assumed
or constructed from its Input.

1. Exact interface

SelectedFactorStatement[l].Over[k,setk].Field packages zero-or-unit
decision for every scalar and 1 != 0. At[S].Input packages that field
structure, a finite rank and TraceBasis.Basis, the unit determinant of
the trace Gram matrix, and a specified decidable propositional prime.

At[S].Selected[n,basis,q] contains:
- an idempotent e with e^2=e and e outside q;
- a generator x and a coefficient list lower;
- e*P(x)=0, with P=monic lower obtained by appending leading coefficient 1;
- w with e*(P'(x)*w-1)=0;
- one coefficient list for each basis vector b_i, with
  e*(b_i-representation_i(x))=0.

The derivative P'(x) is exactly the second component of the dual-number
Horner evaluation used by Introduction.slope. The identity is stated in
the ambient algebra so the residual bridge can retain powers of its
localization element. There is no factor quotient or complete product
decomposition in this interface.

SelectedPolynomial.Over[k,setk,S,x].At[n,basis,e,p,hp] constructs an
actual polynomial representation of every a by taking the same finite
coordinate combination of the lists p_i. Its generates theorem proves
e*(a-representation(a)(x))=0. Thus finitely many representatives suffice
without global choice.

2. Checked algebraic facts

PrimeIdempotents: the record Prime has ideal laws, propositional
membership, properness, primality and decidable membership. At[q].choose
selects exactly one side of any idempotent decomposition. Regular[a,b,h]
constructs a*b and its complementary annihilator from a=a^2*b.

IdempotentFactor.Over[A,setA,e,he] constructs eA as the fixed-point subtype
of multiplication by e, with unit e, a commutative set-ring structure,
and surjective ring projection A -> eA. Enumerations project to finite
enumerations of eA. Selected[q,outside,kills] proves the kernel is exactly
q and the factor is nonzero. Its inverse/field theorems use regularity of
A: for nonzero x, x*(1-x*b)=0 puts 1-x*b in q; multiplying by e produces
an inverse e*b. Mere regular witnesses are eliminated only into the
proposition that a fixed element is a unit.

FinitePrimeFactor.Over[A,setA,q].Enumerated[n,enumeration,covers].theorem
  regular : Trunc Result.
The enumeration may have repetitions and covers only merely. Filter its
values into q, choose the finitely many regular witnesses under
truncation, and multiply complementary annihilators. The result e is 1
modulo q, outside q and kills q. Factor[r] then exposes the constructed
finite nonzero field from IdempotentFactor. No arbitrary representative
choice or ideal-basis algorithm is used.

ReducedIntegralRegular.Over[k,setk,dec,S,reduced].from-annihilator a lower
  root : PrincipalRegularity.Over[S.ring].Witness a.
Here reduced only needs square-zero elements to be zero. A monic
annihilator is stripped from the constant end. Zero coefficients use
(a*b)^2=(a^2*b)*b; the first nonzero coefficient is inverted to construct
the witness a=a^2*b INSIDE S. The regular theorem accepts mere monic
annihilators for every element and gives regularity, without asserting
that an ambient witness belongs to a subalgebra.

DiscreteCoordinates.Over[k,setk,field].At[S,n,basis].decide gives decidable
equality in S by comparing finitely many coordinates. Its zero decision
supplies the field-decision input of the selected factor. This uses an
actual basis, not finite generation alone.

3. Minimal polynomials, module presentations and trace

FieldPolynomialDivision gives bounded division by a polynomial with an
invertible leading coefficient. FieldPolynomialEuclid constructs an
extended gcd, with both divisibility and Bezout certificates, by bounded
recursion. The zero-polynomial cases are included.

FieldLinearMembership uses GaussianQuotient to decide membership in the
span of finitely many coordinate vectors and gives actual coefficients
when membership holds. PowerSpan applies this to successive powers.
MinimalPolynomial.Over[k,setk,field,S,n,basis,x].theorem merely supplies
the least-degree monic relation; the determinant trick bounds the search.
from-annihilator is actual. Given[f].Divides proves that every polynomial
annihilating x is a multiple of f. No trace assumption is used.

MinimalPolynomialInjection.Over[k,setk,field,S,n,basis,x].At[f] constructs
Q=k[T]/f, its canonical finite basis, and an injective algebra map
hom:Q->S taking T to x. Minimality kills the bounded normal remainder of
any kernel element. Thus Q itself is a finite-basis model of k[x].
Reduced[reduced].regular constructs regularity inside Q, and Prime[q]
pulls back a decidable prime. Monogenic[generated] gives an actual inverse
algebra homomorphism and equivalence when every element of S merely has
a polynomial representative in x; the fibres are propositions, so no
representative choice is needed.

FiniteAlgebraModulePresentation.Over[k,setk,A,S,h,m,n,ab,sb] gives a finite
A-module presentation of S from finite k-bases of A and S. Its generators
are the S-basis vectors b_j; its relations are
 a_i*u_j - sum_t iota_A(coord_t(h(a_i)*b_j))*u_t.
The exact identity c-eta(phi(c))=sum_ij coefficient_ij*relation_ij gives
ACTUAL kernel witnesses. linear, onto, killed, kernel-merely match the
Gaussian quotient interface. Neither a field nor injectivity is needed.

TraceLinear proves rectangular trace cyclicity. PerfectTraceNondegenerate
deduces nondegeneracy from an invertible Gram determinant.
TraceRetraction transfers the trace and its nondegeneracy to an
idempotent factor with a given basis; its inclusion may send 1 to e.
TraceTransitivity proves Tr_S/k=Tr_A/k composed with Tr_S/A from an
ACTUAL relative A-basis. Its Descend transfers nondegeneracy to an
injectively embedded A. These results avoid product-basis and full
discriminant-transitivity formulas, but do not construct a relative basis.

TraceDerivations kills every self-valued k-derivation of an algebra with
nondegenerate trace: [bD,m_a]=m_(bD(a)), so all trace pairings of D(a)
vanish. MonicDualValues proves P(x+h*epsilon)=(P(x),P'(x)*h), and its
Natural module transports the derivative through algebra maps.
RelativeDerivations is the linear-map/Leibniz interface, with Retarget
for pointwise equal structure maps. MonicRelativeDerivation constructs
an actual Q=k[T]/P -> T derivation from a derivative annihilator at a
root in T. Its generator equation is D(T)=h; slope-is compares the monic
value convention with the exact ordinary dual-Horner slope.

MonicTraceSeparable is the self-target version: nondegenerate trace
kills derivative annihilators in Q. Regular[nondegenerate].theorem then
gives an inverse derivative. Reduced[dec,reduced,nondegenerate].ordinary
constructs regularity via FiniteReducedRegular and gives an inverse for
the ordinary dual-Horner slope. Its reducedness and nondegeneracy inputs
are explicit; this file does not assert them for every monic quotient.

4. Regression and validation

PrimitiveRegression uses F2 x F2 and the prime defined by the first
projection. The finite construction computes e=(1,0), kills the other
factor, and supplies inverse witnesses, a field decision and an explicit
finite enumeration of eA. It also computes regular witnesses from the
annihilator T^2-T, constructs a two-vector basis and its perfect trace,
and supplies a selected monogenic certificate (generator 0, P=T) whose
finite representations extend to every element.

The later regressions run extended Euclid (including zero), construct a
minimal polynomial, compare trace on the first factor and in a tower,
and give actual coefficients for a nonzero module-kernel vector. The
polynomial identity (a,b)=b+(a+b)*T at T=(1,0) supplies the monogenic
hypothesis, so the minimal quotient is actually proved isomorphic to
F2 x F2. Its prime, regularity and a dual-root derivation are instantiated.

Fresh All.seg --opened: 9219 declarations, 0 failed, 3.97 seconds.
./segc sag/etale-field-primitive all: 216 modules, 0 failed, 3.16 seconds.
1160 owned declarations in 25 files; all 1160 are listed in the opens
specification and each reports "nothing else opened". Every owned
declaration takes at most 0.06 seconds. Generic proofs open at most 33
definitions; computed regressions open at most 38. The largest generic
lists expose the existing presented quotient's carrier/operation aliases
and its universal map while taking its components; no shared module was
changed to remove those boundary unfoldings. Regressions intentionally
execute the finite product construction and finite arithmetic tables.

Two mutations failed and were restored: the selected factor was changed
to (0,1), and the derivative inverse in the selected certificate was
changed from 1 to 0. The restored regression rechecks.

Original owned proof files:
PrimeIdempotents.seg, IdempotentFactor.seg, FinitePrimeFactor.seg,
SelectedFactorStatement.seg, SelectedPolynomial.seg,
ReducedIntegralRegular.seg, DiscreteCoordinates.seg,
PrimitiveRegression.seg.
Additional owned files:
FieldPolynomialDivision.seg, FieldPolynomialEuclid.seg,
FieldLinearMembership.seg, PowerSpan.seg, MinimalPolynomial.seg,
TraceLinear.seg, PerfectTraceNondegenerate.seg, TraceRetraction.seg,
TraceTransitivity.seg, TraceDerivations.seg,
FiniteAlgebraModulePresentation.seg, FiniteReducedRegular.seg,
MonicDualValues.seg, MonicTraceSeparable.seg,
MinimalPolynomialInjection.seg, RelativeDerivations.seg,
MonicRelativeDerivation.seg.
Other proof files are relative links. No shared/checker files were
changed, no new axioms introduced, and nothing committed. All.seg retains
the existing univalence/replacement/surjection parameters.

5. Remaining primitive-element construction

This directory proves the ingredients above, not the complete selected
primitive-element theorem. Selected relative bases and the assembly of
selected separable annihilators live in separate developments. The
relative basis requirement in TraceTransitivity is not an axiom or a
claim that this directory constructs it.

The large-field branch must construct a nonzero discriminant polynomial
for a generic primitive combination, with an explicit degree bound and
a successful scalar from sufficiently many distinct candidates. The
small-field branch is developed separately in etale-field-small-branch,
using the constructed finite coefficient field and finite-field primitive
element. The selected finite field in this directory supplies only the
factor algebra, not its primitive generator.

SMALL-FIELD-PLAN.txt preserves the earlier informal plan. Parts of its
selected-factor and internal-regularity steps are now covered by the
checked files above. It is still a plan for the remaining construction,
not a second claim of a completed theorem.
