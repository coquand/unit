SAG Section 3.1, the axioms of 2.1, and Proposition 3.3.4
======================================================

Worker A's development. All.seg checks this directory and its dependencies.
Section3.seg additionally checks Worker B's tensor/ development and the
integration lemmas in Section3Examples.seg. Worker B's files are unchanged.

Check from the repository root:
  ./segc sag/affine all

For an independent full check, without a checking server or --only:
  checker=$(cabal list-bin exe:seg)
  (cd sag/affine && "$checker" All.seg && "$checker" Section3.seg)

Foundation: the existing univalence and replacement parameters, from
which function extensionality, truncation and effective set quotients
are derived. No new foundational axiom or checker change. Uniform SQC,
Loc and Z-choice are explicit hypotheses where used. No resizing,
excluded middle, or choice over points of a spectrum is assumed.

Public conventions
------------------
Algebras[l].Over[R,setR]: Algebra, genuine R-algebra Hom, Spec.
Presentations[l].Over[R,setR]: finite equation syntax, Presents, FP, SQC.
Ring[l]: Nat, rings and lists. Presentations[l].Fin: finite indices.
FP A is a proposition in U l+; an algebra's carrier and spectrum are in
U l. Constructions from FP produce merely existing witnesses with UP,
not a chosen presentation.

See ../SEC3-INTERFACE.md for the localization interface.

Statements and proofs
---------------------

SAGAxioms.seg: Section 2.1.
  Loc is nontriviality and the local-ring disjunction for an invertible
  sum. SQC is the existing uniform evaluation equivalence for all FP
  algebras. ZChoice gives a finite unimodular family and local sections
  from pointwise mere inhabitants. The family universe k is independent
  of the ring universe l. These axioms are stated, not proved in a model.

FunctionAlgebra.seg, AffineUniqueness.seg: 3.1.1--3.1.3.
  AffineWitness X = (A : Algebra) * FP A * Equiv X (Spec A).
  Affine X is its propositional truncation.
  R^X is an actual R-algebra with pointwise operations.
  Under SQC, evaluation at points X -> Spec(R^X) is an equivalence for
  affine X, and R^X is finitely presented.
  The entire AffineWitness X, including the spectrum identification, is
  a proposition. The proof compares both algebras with R^X and uses a
  structure identity lemma retaining their X-indexed points.
  AlgebraPointsIdentity.seg proves that lemma by univalence; it does not
  assume a ring/algebra structure identity axiom.
  AlgebraInverse.seg inverts a homomorphism with an equivalence as its
  underlying function and transports finite presentability.

AffineUnits.seg: 2.2.3(a) and 3.1.4.
  Uniform SQC and 1 != 0 give unit(a) iff a != 0, using the constructed
  quotient R/(a) and its ideal certificate.
  For a finite family a_i, product_i(x-a_i) is a unit iff every x != a_i.
  This is the pointwise standard-open assertion of Example 3.1.4.

AffineOpens.seg, OpenTransitivity.seg: 3.1.5 and 3.1.7.
  A subtype is proposition-valued; IsOpen means it is merely a finite
  union of principal opens. Under SQC and 1 != 0 this is equivalent to
  the finite nonzero description in 3.1.5.
  Every element of A_f is merely h/f^k (LocalizationFractions.seg).
  Consequently an affine open in Spec(A_f) is a finite union of D(h_i*f)
  upstairs in Spec A, contained in D(f). AffineOpens.Localized.transitivity
  states that its direct image under restriction is affine-open.
  These transitivity and fraction proofs need no geometric axiom.

Localization.seg, AffineInterface.seg: 3.1.6.
  Adjoin a variable y and the equation f*y-1, using a mere expression for
  f in any presentation of A. The resulting finitely presented algebra
  has the canonical universal property, for every target algebra B:
    Hom(A_f,B) = (h : Hom(A,B)) * unit(h(f)).
  At B=R this is Spec(A_f) = D(f), with restriction as forward map.
  LocalizationComparison.seg constructs canonical inverse maps between
  any two localization witnesses.

FiniteQuotient.seg, EquationExtension.seg.
  Append finitely many equations, for arbitrary elements f_i of A:
    Hom(A/(f_i),B) = (h : Hom(A,B)) * (forall i, h(f_i)=0).
  Its spectrum is the simultaneous zero locus. Both constructions
  preserve finite presentability, without choosing from a truncation.

LocalizationNilpotence.seg: 3.1.8.
  D(f) is empty iff f is nilpotent, under SQC and 1 != 0.
  The algebraic implication A_f=0 -> f nilpotent is proved by mapping to
  A[Y]/(fY-1), extracting a polynomial certificate and comparing its
  coefficients (LinearPolynomialCertificate.seg).

StandardOpens.seg, AffineCovers.seg: 3.1.9 and its final corollary.
  D(f) is contained in the union of D(g_i) iff merely
    f^k = sum_i g_i*c_i
  for some k and coefficients c_i. The inclusion-to-certificate proof
  uses the quotient by the g_i, 3.1.8, and QuotientCertificate.seg.
  The reverse implication uses Loc. The combined statement has explicit
  Loc and uniform SQC parameters.
  A finite union of D(f_i) covers iff the family f_i is unimodular.
  FiniteIdeal.seg and FiniteIdealInterpretation.seg interpret the
  quotient's finite derivation trees into actual ideal certificates.

UniformChoice.seg: 3.3.4.
  For FP A and an upwards closed proposition-valued family P(x,n),
    (forall x, || (n : Nat) * P(x,n) ||)
      -> || (N : Nat) * (forall x, P(x,N)) ||.
  Hypotheses: the Loc, uniform SQC, and ZChoice fields of SAGAxioms.
  Z-choice gives finitely many local sections. The localization UP
  transfers each to a finitely presented spectrum, and UniformBounded
  bounds it. Finite choice combines the mere bounds. Their sum is a
  common bound; upward closure and the covering property finish.
  This uses the existing shorter proof of 3.3.3; Worker B's independent
  paper-route proof is also checked by Section3.seg.

Checks and integration
----------------------
AffineExamples.seg checks localization at zero (target collapses), at
one (an actual algebra retraction), quotient by one, quotient by no
equations, recovery of the point, and non-nilpotence of one under 1 != 0.
Three #fails reject false reflection from the zero localization, a
purported automatic retraction, and a forged nilpotence proof. Two
additional negative tests come from the presentation dependencies.

Section3Examples.seg uses Worker B's tensor and arbitrary-map pullback
constructions to inhabit Worker A's Affine predicate, then obtains the
canonical finitely presented function algebra of the pullback.

Dependencies are symlinks to presentations/ and tensor/. All proofs are
in the existing prototype. This is abstract univalent mathematics under
the stated geometric hypotheses, not their interpretation in a model.
