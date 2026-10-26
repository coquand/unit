Jacobian regularity: Step II with explicit annihilator stabilization
===================================================================

Check from unit/:

    ./segc sag/jacobian all

Main theorem
------------

    module D = JacobianDivisibility[l].Over[A,setA,F,G]
    D.result input u v relation

Here F,G are bivariate polynomial expressions with coefficients in A;
u,v are arbitrary elements of the existing polynomial ring A[X][Y].
The hypothesis relation is the actual equality F*u = G*v in that ring.
The result is the propositional truncation of

    (e : Nat) * (w : A[X][Y]) * (J^e * u = G * w).

J is the formal Jacobian determinant. Its partial derivatives are evaluated
by structural recursion with the usual sum and product rules. Equality of
polynomials is equality in the existing coefficient-quotient polynomial
ring, not equality of polynomial functions. ExpressionRepresentation proves
that every element of A[X][Y] admits a bivariate expression, merely.

The one additional algebraic hypothesis
--------------------------------------

Let B = (A[X][Y]/(G))[1/J], constructed in the development, and let f be
the image of F. The parameter input is merely the existence of

    n : Nat
    stable : (v : B) -> f^(n+1)*v = 0 -> f^n*v = 0.

This is D.NoetherianInput, under propositional truncation in D.result.
The reverse inclusion of annihilators is automatic and is not needed.
Noetherianity, its preservation by polynomial extensions, quotients and
localizations, and the reduction to finitely many coefficients are NOT
proved or silently used here. For an arbitrary original coefficient ring,
the remaining task is to supply this input after the appropriate finite
coefficient/universal-ring reduction. Assuming it directly for B gives
the displayed conditional theorem immediately.

Without the stabilization hypothesis (2026-10-26)
-------------------------------------------------

    D.result-coded input u v relation          (JacobianDivisibility)
    CodedCoefficients.Over[A,setA,F,G,PA,nA,onto].result u v relation
    CodedCoefficients.OverZ[A,setA,F,G,as,onto].result u v relation

Stable is not needed. At every order n, the order-n Taylor lift gives the
coefficient w_n with u = f^n w_n and f^(n+1) w_n = 0 (RegularAt.iterated,
RegularAt.killed; StableAnnihilator.Kernel takes Stable only in result).
If some w_k is a combination of w_0..w_(k-1), multiplying by f^k gives
u = 0 (Sequence.Kill). Noetherianity on this one sequence suffices; it
comes from a noetherian presentation of B onto which every element merely
lifts (CodedSubring.CodedNoetherian), walked along codes of the w_n under truncation
(Sequence.Kill.Walk), so no choice is used.

CodedCoefficients builds that input whenever the coefficient ring A has
such a presentation (PA, nA, onto): B is presented by the codes of A with
x, y and 1/J adjoined, noetherian by the Hilbert basis theorem
(sag/noetherian), and every element of B is merely a fraction of an
expression in x, y and constants. OverZ is the case of A generated over Z
by finitely many elements. Bar, Span, Sequence, NatOrder, PolyPres,
Hilbert, Transfer, Generated and Integers are links to ../noetherian.

Arbitrary coefficient ring (no hypothesis at all)
-------------------------------------------------

    FiniteCoefficients.Over[A,setA,F,G].result u v relation

Informal proof: doc/jacobian-noetherian.tex. The generators are the images
in B of the constants of F, G, U, V, with 1/J, y, x; they present Z[gens]
in B, noetherian. B' = the coded subring (CodedSubring: a set-level Sigma
with the propositional predicate "merely has a code"), a ring with the laws
of B and an injective inclusion; it is coded noetherian (Subring: the bar
for the codes in B is one in B'). F, G, U, V are lifted to B' (each
constant is a generator) and RegularAt.Curve is run over B' with the
identity as coefficient map. Curve uses F U = G V only through the curve
identity in B'[T], obtained from the one in B[T] through RawMap (a ring
map on coefficient lists) and the injectivity of B' -> B; no relation in
A0[X,Y] is needed. Each w_n lies in B', so is merely coded, and
CodedSubring.Vanish (Sequence.Kill walked under truncation) gives u = 0 in
B', hence in B. RegularAt.Over is Curve with the curve identity obtained
from the relation in A[X][Y].

Everything after the stabilization hypothesis is proved: the finite Taylor
lift, application to a polynomial identity, the quotient by G, localization
at J, and clearing denominators to obtain the certificate in A[X][Y].
Step I from CAR1.pdf is not part of this directory.
The separate sag/mertens development now proves the univariate
Dedekind--Mertens formula, including the stronger additive-subgroup
statement from mertens.pdf. The multivariate content lemma and its
localization application have not yet been connected to that result.

Proof organization
------------------

FiniteJets: equality below a finite degree and the effect of changing one
coefficient; the product formula for a positive-degree correction.

Bivariate, BivariateNaturality: expressions, evaluation, formal partials,
first-order Taylor at each finite degree, and compatibility with ring maps.

LinearSolve, TaylorLift: inverse of a 2 by 2 matrix from the inverse of its
determinant; construct x(T),y(T) with F(x(T),y(T)) = f-T and G(x(T),y(T)) = 0
modulo T^(n+1). The sign differs from f+T in the informal proof only to
simplify the final recurrence.

StableAnnihilator: (f-T)*p = 0 mod T^(n+1) and stable f n imply p(0)=0.
This includes n=0. The coefficient proof is primitive recursion on n.

PolynomialIdentity, RegularAt: transport a genuine polynomial identity to
the constructed finite curves, and conclude the value of U is zero.

PrincipalQuotient: A/(g), with a proved kernel certificate a=g*w.
PowerLocalization: existing monoid fractions at powers of j, with inverse
of j and a proved power-annihilation kernel certificate.
JacobianDivisibility: combine these results to obtain Step II.

Examples: F=X+X^2, G=Y at (0,0), over every commutative ring. Constructs
all finite lifts and proves the first two coefficients of x(T) are -1;
y(T) vanishes to the requested precision. No characteristic hypothesis.

Foundations and generated identities
-----------------------------------

The same univalence and replacement parameters as the existing polynomial
library are used for effective set quotients and propositional truncation.
No excluded middle, choice, flatness, etaleness, or new checker rule is used.
All recursion is through Unit's data eliminators. Dependencies are relative
symlinks to the existing library; those files are unchanged.

JetIdentities.seg consists of ordinary equality proofs generated from
identities.json by the existing, untrusted ring-identity generator:

    python3 sag/horrocks/ring_normalise.py \
      sag/jacobian/identities.json sag/jacobian/JetIdentities.seg

Unit checks each generated proof; the generator adds no axiom.
