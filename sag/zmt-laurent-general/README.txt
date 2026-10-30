Generic native Laurent chart foundation
======================================

All files are new; shared libraries and previous developments are unchanged.
For every commutative set-ring A, finite coordinate number n and structural
subset E : GenericCube.Sub n, NativeChartRing constructs the localization
of the actual iterated polynomial tower at the product of coordinates E.
The empty chart is the polynomial ring's localization at1. No dimension
or nonempty-chart condition is imposed.

ChartDirections proves denominator exponent arithmetic. TowerLaurentCore
reads the actual polynomial tower into signed coefficient functions,
proves coefficient extensionality and finite support, and compares finite
term-list multiplication with coefficient convolution.

NativeChartRing proves a denominator monomial acts by exponent translation;
this makes its action injective over arbitrary A, including zero divisors.
Localization fractions consequently have well-defined Laurent coefficient
functions. Equality is characterized by coefficient equality, and polynomial
multiplication is the actual finite Laurent polynomial action.
NativeChartSupport proves coefficients vanish at negative exponents outside E.

NativeDegreePart constructs the underlying A-module and degree-k projection
into actual finite-support GenericLaurent.Chart modules (any chart-index
type I, with E fixed). Its Into.lin is proved A-linear. NativeChartAction
constructs homogeneous polynomial action on these modules; and
NativePartMultiplication.Product.equation proves projection of actual native
multiplication agrees with action on the appropriately shifted degree part.
The argument permits arbitrary integer twists, including negative ones.

ChartContainment is structural subset containment, with explicit complementary
denominator exponents. NativeRestriction constructs the corresponding ring
map, proves it preserves polynomial inclusion and every Laurent coefficient.
NativeCoordinates constructs each inverse coordinate on any chart containing
it, proves its coefficient translation formula and pure degree-(-1) support.
Restriction preserves variables and these inverses. CoordinateExponents
provides standard Fin n natural-exponent axes; CoordinateComparison identifies
them with singleton-chart denominator exponents. The newest coordinate is
inr tt. These files have no selected contraction linearity claim.

Exports use Fin n -> Base.Nat ordinary exponents and Fin n -> ZInt.Int signed
exponents, exactly the generic syzygy and Cech interfaces. Finite-support
existence is truncated; no infinite choice, new axiom or resizing is used.

Validation is recorded in VALIDATION.txt and the full opening inventory
zmt-laurent-general.opens. This directory supplies chart algebra; it does
not itself assert the finite-fibre sections or the final ZMT theorem.
