Projective squaring and constant functions: SAG 6.1.9 and 6.2.1
============================================================

Run from primrec:

    ./segc sag/projective all
    ./segc sag/projective changed

The main statements are in Example.seg, Theory.Example[l].SAG:

    P1        : U l
    s         : P1 -> P1
    zero      = [0:1]
    one       = [1:1]
    Disk      = (a : R) * Id R (a*a) 0
    Fibre q   = (p : P1) * Id P1 (s p) q

    zero-fibre : Equiv Disk (Fibre zero)
    two-fibre  : (2 = 0 -> Empty) -> Equiv Bool (Fibre one)

Both equivalences have constructed forward and inverse maps with proofs
of both composites.  For the second, true goes to [1:1] and false to
[-1:1], the latter also being [1:-1].  No assertion that Disk is inhabited
by a nonzero nilpotent is made.

Fibres.seg proves the stronger chart calculation, for every t : R:

    Equiv ((a : R) * Id R (a*a) t) (Fibre [t:1]).

This calculation needs only a commutative set-ring.  The two-point result
first uses locality, 1 != 0, and invertibility of 2 (TwoRoots.seg).
UnitDetection.seg derives invertibility from 2 != 0 using SQC.

Assumptions
-----------

All.seg has precisely the same foundational parameters as replacement/:
univalence, chosen replacement images, and their all-universe surjectivity.
Function extensionality is derived from univalence.  Truncations and
effective small set quotients are derived, not additional axioms.

Example.SAG additionally takes a commutative ring with a set-valued carrier,
nontriviality, locality, and the following family of SQC instances:

    evaluation : R/(x,y) -> ((x=0)*(y=0) -> R)  is an equivalence.

LinearIdeal.seg constructs R/(x,y) as the quotient by
    a ~ b := || (c d : R) * a = b + x*c + y*d ||
(with the indicated parenthesization in the source), and constructs this
evaluation map.  Its equivalence is the explicit SQC hypothesis; it is
not postulated to follow from replacement.  These are the finite
presentations used in SAG Proposition 2.2.3.  We do not formalize the
general category of finitely presented R-algebras, its homomorphism-based
spectrum, or the restriction of a general SQC interface to these instances.
The spectrum of this particular presentation is represented directly by
the equations x=0 and y=0.  Z-choice is not used.

Construction and checked links
------------------------------

Quotient.seg constructs effective small quotients from replacement as the
image of a -> (x -> relation x a).  It proves setness, proposition-valued
dependent induction, both directions of effectiveness, and descent of
relation-preserving maps into sets, with a propositional beta rule.

Projective.seg glues the two affine charts by a*b=1.  Squaring descends
because this relation is preserved by a -> a*a.

Coordinates.seg defines [x:y] when merely one coordinate is a unit, proves
independence of normalization, invariance under unit scaling, and the
formula s([x:y])=[x*x:y*y].  No choice of chart is assumed.

Homogeneous.seg proves that the chart quotient is equivalent to the
quotient of unimodular pairs by unit scaling, with both inverse laws.

UnitDetection.seg derives the two-coordinate nonzero/unit-cover property
and nonzero implies invertible from the stated SQC instances and locality.

Example.seg proves that nonzero pairs and unimodular pairs are equivalent,
that every P1 point merely has a nonzero representative, that any scalar
relating nonzero pairs is a unit, and that equality of projective points
is equivalent to the mere existence of a scalar relating representatives.

Scope
-----

This completes the two fibre equivalences suggested for Example 6.1.9,
including the projective construction and homogeneous squaring formula.
The example's further assertion about all fibres having coordinate
algebras free of rank two is not formalized here.  Nor does this development
interpret the axioms or these constructions in the presheaf model.

Isolation
---------

No checker, defenv, core, replacement, or sag source was edited.  The core
and replacement dependencies are relative read-only symlinks, and Ring.seg
links to polynomial/Ring.seg, the shared ring library (sag/Ring.seg plus
the shared elementary ring lemmas).  The development has its own
checking server in projective/.segserver-d (ignored by git).

Nothing is committed.  The theorem declarations themselves are checked
in the full run; no trusted-only check, omitted proof, or extra proof
postulate is used.

Constant functions: Lemma 6.2.1
------------------------------

ConstantFunctions.seg proves, on the same P1 as the squaring example:

    constant (f : P1 -> R) (q : P1) : Id R (f q) (f [0:1])
    functions-equivalence : Equiv R (P1 -> R)

The latter sends c to the constant function with value c; its inverse is
evaluation at [0:1].  Both inverse equations are proved.  The SAG adapter
exports the statement as lemma-6-2-1 on Example.SAG's P1.

The additional mathematical hypotheses are the SQC evaluation instances
for R[X] and R[X,X^{-1}].  They are not claimed to follow from the earlier
instances for R/(x,y).  The only foundational axioms remain univalence
and replacement, with function extensionality and the quotients derived.

PolynomialFunctions.seg represents R[X] by coefficient lists, modulo
coefficient equality (including trailing zeros), and defines evaluation
by Horner recursion.  Affine SQC states that this evaluation map to
(R -> R) is an equivalence.  It gives mere polynomial representatives
of the two chart restrictions; no global choice of lists is needed.

LaurentFunctions.seg represents Laurent polynomials by pairs (p,n),
meaning p(X) + X^{-1} n(X^{-1}), modulo coefficient equality on each list.
In particular the constant coefficient occurs only in p.  Torus SQC
states that evaluation on ((x:R)*(y:R)*Id R (x*y) 1) is an equivalence.
These are explicit SQC interfaces in coefficient presentations; a general
algebra library and the identification with a separately implemented
bivariate quotient R[X,Y]/(XY-1) are not part of this development.

The module Laurent.Intersection contains the pure coefficient calculation,
without SQC: if the Laurent images of p(X) and q(X^{-1}) agree, all their
positive-degree coefficients vanish and their constants agree.  The
Comparison module uses only injectivity from torus SQC to obtain that
coefficient equality from agreement of the functions on the overlap.

ConstantFunctions.seg obtains the overlap equation by applying f to the
checked projective gluing path, applies the comparison, and eliminates
over the projective quotient to prove constancy everywhere.  Loc is not
used in this calculation once P1 is given by its charts; the SAG adapter
retains Loc and the earlier SQC instances for its nonzero-coordinate
interpretation.

This extension adds three source files and their imports in All.seg.
All previously checked geometric proofs are unchanged.
