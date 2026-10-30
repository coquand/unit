Native four-coordinate chart Laurent rings
==========================================

1. Checked result

This directory constructs actual commutative chart Laurent rings and the
coefficient/degree-projection interfaces needed for finite-fibre sections.
It does not assume a Laurent ring, chart multiplication laws, a localisation
universal property, chart restriction maps, or coordinate inverse laws.

For every commutative set-ring A and chart subset E of the four homogeneous
coordinates, put S=A[X0][X1][X2][X3] and let J_E be the product of exactly
the inverted coordinates. The native chart ring is the existing constructed
power localisation S[1/J_E]. Its Laurent coefficient map is constructed
and injective; every element has truncated finite coefficient support,
and all coefficients at exponents forbidden on E vanish.

The construction also supplies coefficient-preserving ring restrictions
E subset F, explicit inverses of every coordinate inverted in E, their
shifted-delta coefficients, A-linear fixed-degree projection to actual
Laurent4 chart modules, and compatibility of homogeneous polynomial
multiplication with that degree projection.

There are 11 new .seg files and 529 new declarations. Older sources are
relative symbolic links to ../zmt4. No shared source, previous development,
checker or .git was modified. No new axioms, infinite choices or resizing
assumptions were introduced; All.seg has the inherited foundational
parameters. Nothing is committed.

2. Precise informal argument and declarations

LaurentPowerRing4 (127 declarations)
  First construct the full chart at J=X0 X1 X2 X3. Polynomial monomial
  multiplication reads shifted coefficients (Term.result, term-action).
  Four named reassociations avoid repeatedly unfolding iterated quotient
  operations. phi-action extends this to arbitrary finite term lists.
  diag(n)=(n,n,n,n), with Ring/Base natural conversions stated explicitly.
  psi-power proves psi(J^n*x)(m)=psi(x)(m-diag(n)); evaluating at
  m+diag(n) proves power-inj, even when A has zero divisors.

  The EXISTING PowerLocalization supplies an actual CRing. A raw fraction
  q=(a,s,n,s=J^n) has coefficient psi(a)(m+diag(n)). exact cancels the
  auxiliary annihilator in a fraction relation using power-inj. Compare
  then shifts the exact cross-multiplication equality by the two denominator
  exponents; raw-respects-exact and raw-respects descend coefficients
  through the existing effective quotient. Coeff.beta gives coeff-fraction.
  coeff-inclusion identifies ordinary polynomial coefficients.

  AddRaw computes coefficients of a sum after the common denominator
  shift, proving coeff-add. psi-neg and the quotient negation beta rule
  prove coeff-neg; coeff-zero/one follow from inclusion. PolynomialRaw
  uses phi-action and commuting shifts to show that multiplication by
  an ordinary term-list polynomial is EXACTLY the old PolynomialAction4
  action on Laurent coefficients (coeff-mul-polynomial).

  RawExt reverses the denominator-shift computation: equal fraction
  coefficients imply equal polynomial cross-products, hence equal ring
  fractions. ext descends this to coefficient extensionality. For finite
  support, FractionSupport chooses a numerator term list only under
  truncation and translates its explicit support by -diag(n). raw-finite
  and finite keep all such representatives truncated.

ChartLaurentRing4 (115 declarations)
  Parameterise the same native construction by a chart subset E. The
  scalar entry(f,n) is n for an inverted coordinate and 0 otherwise.
  direction(E,n) replaces diag(n); entry-step/plus and direction-up give
  the same denominator and translation laws without a sign table.
  Its Over[A,setA,E] exports the same constructed ring, coefficient,
  equality, finiteness and polynomial-action interfaces. The polynomial
  term-action proof is reused from the full-chart stage.

ChartCoefficientSupport4 (15 declarations)
  out-entry shows that a forbidden negative coordinate outside E is
  unchanged by direction(E,n). out-direction turns such a coordinate into
  a negative coordinate of the ordinary numerator. A polynomial coefficient
  vanishes there (polynomial-negative), using its truncated representative
  and the earlier FinitePolynomial4.cf-neg theorem. Quotient induction
  therefore proves van for EVERY native chart ring element. In particular,
  all native ring sums/products/powers remain chart-supported automatically.

ChartDegreePart4 (44 declarations)
  Compose the actual polynomial constant inclusions and the localisation
  inclusion to construct iota:A->R_E. moduleM is its actual underlying
  A-module, and coeff-sm proves its scalar coefficient law using the
  old finite-polynomial action. Part[k].value selects coefficients of
  projective degree k. van proves the required degree/chart vanishing.
  Into[I].support preserves the finite exponent list, so Into.element is
  an ACTUAL element of Laurent4.Over.Chart[I,constant Bad(k,E)].
  The coefficient addition/scalar laws prove Into.lin is A-linear.
  No homogeneity of an input ideal-witness coefficient is required.

ChartPartMultiplication4 (30 declarations)
  For a homogeneous polynomial p of natural degree dd, degree-shift
  identifies deg(m-u) with k-dd when deg(m)=k. read-terms proves the
  action reads only that input part. Off degree k the constructed actual
  homogeneous action already vanishes. Product.equation combines these
  two cases with coeff-mul-polynomial to prove actual chart equality:
      Part_k(include(p)*x) = p * Part_(k-dd)(x).
  This is the interface for projecting arbitrary J-witness coefficients.

PowerLocalizationToUnit (38 declarations)
  Construct the universal map S[1/j]->R whenever f:S->R and f(j) has a
  specified inverse. mapF sends a/s to f(a) times the constructed inverse
  of f(s). fraction proves its denominator equation. cancel and solve
  remove invertible denominators from the image of a fraction relation;
  respect descends the map. add-denominator/mul-denominator prove its
  ring laws by cancelling the common invertible denominator. hom is an
  ACTUAL RingHom, and constant proves its inclusion comparison. These
  main laws are proved, not universal-property parameters.

ChartRestriction4 (42 declarations)
  The complement of E inside F is computed flagwise. entry-sum/mask-sum
  prove J_E*J_complement=J_F as an ordinary polynomial identity. Since
  J_F is invertible in the F-chart, invertible constructs an explicit
  inverse of J_E there. Instantiate PowerLocalizationToUnit to get hom.
  To prove coefficient preservation, coeff-power shows multiplication by
  the image of J_E^n reads the -direction(E,n) shift. Apply the map's
  denominator equation and undo that shift; Fraction.result and
  coefficient give the coefficient comparison for every element.

ChartCoordinates4 (44 declarations)
  unitN(k) is the old ordinary coordinate monomial; single-exp identifies
  it with the denominator of the single-coordinate chart. Its restriction
  inverse constructs inverse and law for any chart containing k.
  coefficient-variable is the ordinary negative shift. Evaluate the unit
  law at m+e_k to obtain coefficient, the shifted delta function for X_k^-1.
  degree proves this inverse is homogeneous of degree -1. cancel-inverse
  and coefficient-inverse-mul give its positive shift on arbitrary chart
  elements. Restriction.variable follows from the ordinary inclusion
  comparison, and Restriction.Inverse.equation follows by uniqueness of
  the inverse in the target ring.

ChartInversePart4 (20 declarations)
  The degree -1 part of an inverse coordinate is the whole inverse
  coefficient function: projection follows by the degree test and the
  proved inverse degree law. coefficient gives EXACTLY
      Part_-1(X_k^-1)(m) = FinitePolynomial4.delta0(m+e_k),
  the required Z-chart normalisation when k=p0.

ChartRestrictionNaturality4 (24 declarations)
  le-self constructs chart reflexivity. Identity.equation and
  Composition.equation follow from coefficient preservation and the proved
  target coefficient extensionality, so restrictions compose as expected.

3. Public APIs

ChartLaurentRing4.Over[A,setA,E]
  B.S / S                 actual four-variable polynomial ring
  ring, set               actual native chart Laurent CRing and sethood
  inclusion               RingHom S ring
  coeff x m               Laurent coefficient in A
  coeff-fraction q m      coeff(include(a/J_E^n))(m)=psi(a)(m+direction(E,n))
  coeff-inclusion x m     coeff(inclusion(x))(m)=psi(x)(m)
  coeff-polynomial p m    coeff(inclusion(phi(p)))(m)=old FP.cf(p)(m)
  coeff-mul-polynomial    coeff(inclusion(phi(p))*x)=old PA.mulP(p,coeff(x))
  coeff-add/neg/zero/one  exact coefficient laws
  ext                     coefficient equality implies actual ring equality
  finite x                truncated explicit list supporting coeff(x)

ChartCoefficientSupport4.Over[A,setA,E].van x m
  : Out E m -> coeff(x)(m)=0.

ChartDegreePart4.Over[A,setA,E]
  iota : RingHom A R_E
  moduleM : A-module on R_E
  Part[k].value x m
  Part[k].Into[I].element x : actual homogeneous chart cochain
  Part[k].Into[I].lin : Lin[A,moduleM,Chart[I,constant Bad(k,E)].mod]

ChartPartMultiplication4.Over[A,setA,E]
 .Product[k,dd,p,hp].equation x
  : Part_k(include(p)*x)=p*Part_(k-dd)(x), ACTUAL chart-module equality.

ChartRestriction4.Over[A,setA,E,F,le]
  hom : RingHom R_E R_F
  constant : hom(inclusion_E(s))=inclusion_F(s)
  coefficient x m : coeff_F(hom(x))(m)=coeff_E(x)(m)

ChartCoordinates4.Over[A,setA,E]
  variable k = inclusion(B.term A.o (unitN k))
  Inverse[k,has].inverse
  Inverse[k,has].law : variable(k)*inverse=1
  Inverse[k,has].coefficient m : coeff(inverse)(m)=old delta0(m+e_k)
  Inverse[k,has].degree m ne : coeff(inverse)(m)=0 off degree -1
  Inverse[k,has].coefficient-variable x m : coeff(variable(k)*x)(m)=coeff(x)(m-e_k)
  Inverse[k,has].coefficient-inverse-mul x m : coeff(inverse*x)(m)=coeff(x)(m+e_k)
  has is the existing Le4(setPt k,E), with no assumed unit datum.

ChartCoordinates4.Restriction[A,setA,E,F,le]
  variable k
  Inverse[k,hasE,hasF].equation : restriction preserves coordinate inverses

ChartInversePart4.Over[A,setA,E,k,has].coefficient m
  : degree-(-1) part of inverse = shifted delta0, EXACT normalisation.

4. Checks and limits

Commands from unit:
  timeout 55 ./segc sag/zmt4-laurent-ring all
From sag/zmt4-laurent-ring with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt4-laurent-ring.opens

Results: 187 modules, 0 failed; fresh All.seg 11029 declarations, 0 failed,
about 6.3 s. There are 529 new declarations in 11 files. The complete
529-declaration opening audit reports "nothing else opened" throughout;
at most 36 definitions opened and at most 0.02 s per new declaration.
The explicit profiles include the native localisation, quotient carrier,
operation/beta/accessor aliases and ordinary polynomial coefficient-ring
aliases used at the representation bridges. No choice of a quotient
representative is made as a global function.

ChartRingRegression4 checks Z^-1 on its single chart, restriction to the
{Z,X1} edge, equality with that edge's constructed inverse, exact projected
Z normalisation, homogeneous polynomial/projection compatibility on the
edge, vanishing of negatives on the empty/polynomial chart, and composition
of restrictions to the full chart.

Two isolated temporary mutation copies were rejected: changing the
fraction coefficient translation from m+denominator to m-denominator, and
giving the inverse normalisation the opposite shift. The live sources were
never mutated while the other agents used them.

The ring is a native power localisation with an injective finite Laurent
coefficient map, rather than a separately reconstructed subtype ring of
all finitely supported functions. A general inverse equivalence from an
arbitrary finite coefficient function to the localisation is not packaged.
Signed monomials needed by the sections are available as products of
ordinary variables and the constructed coordinate inverses; there is no
additional flattened signed-term-list representation. This directory
does not construct the finite-fibre sections, ideal/J witness trees,
Rees lifts or final ZMT theorem; it supplies their constructed chart
ring, restriction and homogeneous-projection foundation.
