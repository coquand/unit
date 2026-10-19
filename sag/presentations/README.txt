Finite presentations and uniform SQC
===================================

This directory extends the checked polynomial library without modifying
the prototype, core, polynomial/, bounded/, sag/, projective/ or torsor/.
Polynomial and foundation dependencies are read-only symlinks.
CoefficientBound.seg is an exact snapshot of bounded/Bounded.seg with a
provenance comment; its coefficient proof is reused unchanged.

Check from the repository root:
  ./segc sag/presentations all

Foundation: univalence and replacement, with the same explicit image and
surjectivity schema as polynomial/All.seg. No new foundational axiom.
SQC is an explicit additional geometric hypothesis, not derived from
univalence or replacement. The boundedness theorem additionally assumes
1 != 0; no other part of locality is used.

Algebras.seg
  Over[R,setR].Algebra consists of a commutative ring, a proof that its
  carrier is a set, and a genuine unital ring homomorphism R -> A.
  Hom A B includes the ring laws and compatibility with the structure maps.
  Polynomial[A].algebra is the already constructed coefficient quotient A[X].
  Polynomial[A].To[B].universal proves
    Hom_R(A[X],B) ~= Hom_R(A,B) * B.
  Its forward map is restriction and the image of X.

Presentations.seg
  Fin 0 = Empty; Fin(n+1) = Fin n + Top.
  Expr V has variables, R-constants, sums and products; negative constants
  express subtraction. A presentation is n and a finite list of expressions
  in Fin n, each required to vanish.
  Solutions P B is an assignment satisfying those equations.
  Presents P A consists of a solution in A and equivalence of the CANONICAL
  Hom_R(A,B) -> Solutions P B, for every small R-algebra B.
  FP A is the propositional truncation of the entire presentation witness.
  Uniform SQC says FP A -> isEquiv(A -> (Hom_R(A,R) -> R)), using evaluation.

  Universe accounting is explicit: expressions and solutions live in U l;
  Presents, its witness, and FP live in U l+ because the universal property
  quantifies over all U l algebras. No propositional resizing is assumed.

AddVariable.seg
  added P adds one variable and renames the old equations along the inclusion.
  SolutionsX[P,B].equivalence proves Solutions(added P,B) ~= Solutions(P,B)*B.
  Extension[P,A,presented].presentation proves that the actual polynomial
  algebra A[X] is presented by added P. The proof identifies its canonical
  map with the composite of the two universal properties.
  preserves-FP A : FP A -> FP A[X] eliminates only into a proposition.

BasePresentation.seg
  R has the empty presentation, hence is finitely presented.

UniformBounded.seg
  Theorem[R,setR,one-nz,sqc].ForAlgebra[A,fp].theorem proves
    (f : Spec_R A -> Nat) -> || Sigma N. (x : Spec_R A) -> f x <= N ||.
  The hypotheses are only uniform SQC, 1 != 0, and FP A (in addition to the
  foundational schema and the commutative set-ring/algebra structures).

  Both required SQC instances are derived:
  - A[X] is finitely presented; SQC gives a polynomial representing the
    function on Spec A * R. Quotient induction gives a mere coefficient-list
    representative, which feeds the existing degree-bound proof.
  - R[X] is finitely presented; SQC injectivity and quotient effectiveness
    give coefficient equality from pointwise equality of polynomial functions.
  An adapter converts the new algebra maps to the original coefficient
  proof's tuple format; its weaker structure-map interface adds no hypothesis.

Examples.seg
  Checked instances for R[X], R[X][Y], R presented by (T | T=0), and R[X]
  presented by (T,X | T=0). The last instance exercises a nonempty equation
  list through polynomial extension. BoundedPlane instantiates boundedness
  for Spec_R(R[X][Y]) with its derived finite-presentability witness.

Existence: ExpressionCongruence.seg, CongruenceSoundness.seg,
           PresentedAlgebra.seg, PresentationExistence.seg
  PresentationExistence[l].Over[R,setR,pres].existence has type
    Sigma B : Algebra. Presents pres B.
  This is an actual construction, not only a mere-existence statement.
  The algebra carrier is in U l. Its finite-presentability proof is provided.
  No SQC, normal forms, decidable coefficient equality or resizing is used.

  Expressions are quotiented by the small relation of merely having a valid
  finite derivation. Tree is an ordinary unindexed data type. Its endpoints
  and Valid predicate are defined by primitive recursion; Valid requires
  matching middle endpoints for transitivity. Leaves assert the ring laws,
  coefficient addition/multiplication, or a member of the equation list.
  Negative expressions are (-1)*p. Equality proofs in expressions permit
  coefficient equalities; there is no equality decision procedure.

  The relation is a proposition-valued equivalence and respects both binary
  operations. The existing replacement-based effective quotient supplies a
  set carrier. Operations descend, the ring laws hold, constants form a
  unital homomorphism, and the quotient generators satisfy every equation.

  Soundness is proved in every solution: evaluation respects every valid
  derivation. It therefore descends to a genuine R-algebra homomorphism.
  Expression induction and quotient induction prove uniqueness, giving the
  canonical Hom_R(B,C) -> Solutions(pres,C) equivalence for every target C.
  generated supplies mere expression representatives for the constructed B.

PresentationComparison.seg
  Two algebras with the same presentation have mutually inverse R-algebra
  homomorphisms. Both inverse laws and the underlying carrier equivalence
  are checked; the maps preserve the specified generators.

ExistenceExamples.seg
  The empty presentation is compared with R; the free one-generator algebra
  is compared with the independently constructed coefficient quotient R[X],
  including its generator beta law; the presentation (T | T=0) is compared
  with R. Imposing 1=0 gives a ring in which every element equals zero.
  A #fails test rejects composition with mismatched syntactic endpoints.
  A positive test exercises transitivity and coefficient equality transport.

QuadraticNormalForm.seg: the algebraic part of SAG Example 6.1.9
  Over[R,setR,a].K is the algebra obtained by PresentationExistence for
  the presentation (T | T*T + (-a) = 0).
  normal-form : Equiv (R*R) K.A.Carrier has the EXACT forward map
    (b,c) |-> constant b + constant c * T.
  coefficients is its inverse, expansion and coefficient-beta are the
  inverse laws, and unique proves uniqueness of the two coefficients.
  additive and linear establish compatibility with coordinatewise addition
  and scalar multiplication. Thus this is an R-module basis 1,T, not just
  an equivalence of carrier types.

  QuadraticPairs.seg constructs the independent commutative set-ring R*R:
    (b,c)*(d,e) = (b*d + a*(c*e), b*e+c*d).
  Its universal property for a chosen square root in every R-algebra is
  proved in QuadraticEvaluation.seg and QuadraticNormalForm.seg. Comparison
  with the general presentation quotient proves the normal-form theorem.
  All this works over any commutative set-ring, without SQC or locality.

  QuadraticIdentities.seg contains ordinary ring-law equality proofs for
  associativity, distributivity and the two affine expansion identities.
  They are generated by quadratic_identities.py, which uses distributivity,
  associativity and commutativity only. The Python program is NOT part of
  the trusted proof: seg checks all generated terms. It can be rerun with
    python3 sag/presentations/quadratic_identities.py
  from the repository root; it only writes QuadraticIdentities.seg.

QuadraticFunctions.seg
  Over[R,setR,a,sqc].Root = Sigma x:R. x*x=a.
  spectrum identifies Spec(K.A.algebra) with Root.
  affine-equivalence : Equiv (R*R) (Root -> R) has the EXACT forward map
    (b,c) |-> (x |-> b+c*x).
  It uses the one uniform SQC hypothesis, instantiated at the constructed
  algebra with its derived finite-presentability witness. There is no
  separate assumption about polynomial functions or square-root fibres.
  coefficients, formula, coefficient-beta and unique give the explicit
  coefficient extraction, representation and uniqueness laws.

QuadraticExamples.seg
  Checked instances at a=0 (dual numbers) and a=1, including T*T=0 or T*T=1,
  the coefficients of T, and those of each constant.
  Disk[sqc] specializes to D = Sigma d:R. d*d=0 and proves
    first-order : f(d) = f(0) + slope(f)*d
  for every f:D->R, as well as uniqueness of the slope and the slope of an
  affine function. Neither locality nor invertibility of 2 is assumed.

  These files prove the root-fibre algebra/function statements directly.
  The earlier projective-line fibre equivalence in projective/ has not been
  imported or connected by an adapter; that work is left unchanged.

WeakNullstellensatz.seg: SAG Proposition 2.2.2
  Over[R,setR,sqc].empty-collapse proves that an empty spectrum forces
  1=0 in every finitely presented R-algebra, using uniform SQC.
  collapse-empty proves the converse from 1 != 0 in R.
  all-equal identifies collapse with every pair of ring elements being equal.

PrincipalCertificates.seg and CertificateInterpretation.seg
  Certificate(x,y) = Sigma r. x = y + f*r in any commutative ring.
  Explicit multipliers are constructed for equality, symmetry, transitivity,
  addition and multiplication. No choice is needed to combine certificates.
  CertificateInterpretation interprets the finite derivations defining a
  presentation quotient into these certificates, whenever each equation
  admits a certificate. The truncated relation yields truncated certificates.

PolynomialPresentation.seg and PolynomialCertificate.seg
  A coefficient list is encoded as a Horner expression in one variable.
  Its evaluation agrees with the original polynomial evaluation, and its
  value at the generator of the existing polynomial ring is the original
  polynomial class.
  PolynomialCertificate[l].Over[R,setR,f].of-collapse proves:
    (1=0 in the presented algebra (X | f=0)) ->
      || Sigma g:List R. peq (pmul f g) [1] ||.
  It interprets derivations in the existing polynomial ring and extracts a
  principal-ideal multiplier. Quotient induction then gives a mere list
  representative, and effectiveness gives coefficientwise equality f*g=1.
  This proof requires no SQC and constructs no second ideal quotient.

UniformNullstellensatz.seg: public integration interface
  Over[R,setR,sqc].wn :
    (f:List R) -> Not(Sigma x:R. ev f x=0) ->
      || Sigma g:List R. peq (pmul f g) [1] ||.
  wn-nn has the same input and double-negated output. It matches the other
  worker's revised sag/Mul.seg hypothesis. Only uniform SQC is needed here;
  Loc enters the factorization proof which consumes this theorem.
  CertificateExamples checks extraction for the collapsing presentation
  f=[1] without SQC, the public SQC interface, and rejection of a forged
  ideal certificate.

  ../sag-uniform/ checks the final integration using fixed snapshots of the
  revised sag/ files. SAGUniform.Main.lemma-2-2-4 follows from Loc and
  uniform SQC, with no independent wn assumption. sag/ itself is untouched.

Scope
  Arbitrary finite presentations now have representing algebras. General
  expression-generation for any other algebra with a given presentation can
  be transported along PresentationComparison; that corollary is not yet
  packaged separately. Tensor products, localization, and adding equations
  for arbitrary algebra elements still need their presentation interfaces.
