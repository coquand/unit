Polynomial rings with their universal property
=============================================

Run from primrec:

    ./segc sag/polynomial all
    ./segc sag/polynomial changed

Main interface (within the enclosing Theory segment), at level l:

    module AX = PolynomialRing[l].Extension[A,setA]

A is a commutative ring in the existing CRing format and setA says that
its carrier is a set.  AX exports:

    Carrier             the small quotient type A[X]
    set                 proof that Carrier is a set
    ring                an actual CRing, with every ring law proved
    inclusion           a unital ring homomorphism A -> AX.ring
    constant            its underlying map
    constant-injective  injectivity of the constant inclusion
    variable            X
    include             coefficient list -> Carrier
    horner              include (cons a p) = constant a + X * include p

Addition, multiplication, negation, zero and one are AX.addQ, mulQ, negQ,
zeroQ and oneQ.  Their computation on coefficient lists is expressed by
proved identities (Add.beta, Multiply.beta, Negate.beta); replacement
does not give new judgmental reduction rules for these quotient operations.

RingHom.seg defines Hom A B as a function together with proofs that it
preserves one, addition and multiplication.  Preservation of zero and
negation is derived.  It includes identity, composition, extensionality
and proof that Hom A B is a set when B is a set-ring.

Universal property
------------------

For any commutative set-ring B, let

    module UP = Universal[l].Property[A,B,setA,setB]

Then

    UP.universal : Equiv (Hom AX.ring B) (Hom A B * B.R)

sends g to (g composed with inclusion, g(X)).  Its inverse is constructed
by Horner evaluation on lists followed by quotient descent.  Both inverse
equations are proved, including equality of the homomorphisms with their
law proofs.

For a specified homomorphism f:A->B and b:B:

    UP.Given[f,b].extend        the unique extension A[X] -> B
    UP.Given[f,b].on-constants  extend(i(a)) = f(a)
    UP.Given[f,b].on-variable   extend(X) = b
    UP.Given[f,b].restriction   extend composed with i = f
    UP.Given[f,b].unique        every hom with these two properties equals extend

For a fixed structure map f:A->B:

    UP.Over[f].AlgebraHom
      = (g : Hom AX.ring B) * Id (Hom A B) (UP.restrict g) f

    UP.Over[f].universal-over : Equiv UP.Over[f].AlgebraHom B.R

This is precisely Hom_A(A[X],B) ~= B, not only the special case of maps
into the original base ring used in the boundedness example.

Substitution.seg instantiates the universal property with B=A[X].
It constructs substitution by any polynomial as a ring homomorphism,
and proves substitution by X is the identity and the composition law.

Construction and proof dependencies
-----------------------------------

RawLaws.seg proves the additive and scalar laws coefficientwise.
RawMultiplication.seg proves multiplication respects coefficient equality,
is associative and commutative, has a unit, and distributes over addition.
These are algebraic list-induction proofs; they do not use SQC or equality
of polynomial functions to infer equality of coefficients.

PolynomialRing.seg quotients lists by coefficient equality.  This identifies
trailing zeros without assuming decidable equality in A.  Binary and unary
operations descend to the quotient; all ring laws then descend by
proposition-valued quotient induction.

Evaluation.seg generalizes the evaluation argument from bounded/Bridge.seg
to an arbitrary target ring and a genuine ring homomorphism A->B.
Universal.seg proves uniqueness by induction on the Horner decomposition,
then by quotient induction.

Foundational parameters are univalence and replacement, as in replacement/.
Function extensionality and the effective small quotient are derived.
There are no SQC, Loc, choice, or additional algebraic axioms.

Isolation and reuse
-------------------

Everything newly written is in this directory.  Ring.seg and Poly.seg are
fixed snapshots of sag's files; Mul.seg extracts the unchanged MulR module
from sag/Mul.seg.  The original files and bounded/Bridge.seg were not edited.
The snapshots prevent simultaneous edits by another LLM from changing the
inputs of this check.  The existing examples have not been migrated to
this interface.

Core and replacement files are relative symlinks; Quotient.seg is a relative
symlink to the checked effective quotient construction in projective/.
No checker implementation was changed.  Nothing is committed.
