SAG Sections 3.2 and 3.3: tensor products, pullbacks, boundedness
=================================================================

Check from the repository root:
  ./segc sag/tensor all

Builds on ../presentations without modifying it; the shared files are
read-only symlinks to ../presentations.  Foundation as there: univalence
and replacement, nothing else.  SQC (uniform, from Presentations.seg) and
1 != 0 are explicit module parameters where they are used.

FinSum.seg
  Concatenation of presentations.  Fin(m+n) with the two inclusions
  left/right, case analysis `cases`, and its uniqueness.
  tensor p q has the variables of both and the equations of both, renamed.
  Split[p,q,B].equivalence : Solutions(tensor p q, B) = Solutions(p,B) * Solutions(q,B).

Tensor.seg: 3.2.1
  Coproduct A B T: maps inA, inB, and Hom(T,D) -> Hom(A,D) * Hom(B,D),
  h |-> (h inA, h inB), an equivalence for every algebra D.
  spec-product : any coproduct T has Spec T = Spec A * Spec B (D = R).
  Construction: the algebra presented by tensor p q is a coproduct of
  algebras presented by p and q.  Presented: the one built by
  PresentationExistence.  exists : FP A -> FP B -> || Tensor A B ||,
  where Tensor A B = (T : Algebra) * Coproduct A B T * FP T.
  No SQC.  Any two coproducts are isomorphic, so nothing depends on the
  presentations chosen.

Generated.seg
  In an algebra A presented by p, every element is merely the value of an
  expression in the generators (via PresentationComparison with the
  constructed algebra, whose elements are expression classes).
  choice: finite choice for propositional truncation, over Fin c.

Pushout.seg: 3.2.2, algebraic part
  For f : K -> A, g : K -> B, a cocone is (h, k) with h f = k g, and a
  pushout T has Hom(T,D) = Cocone(D).  For presented A, B, K and
  expressions e_v, e'_v for f(c_v), g(c_v) (c_v the generators of K), the
  presentation tensor p q plus the equations e_v - e'_v presents a pushout.
  Exists.exists: FP A, FP B, FP K give merely a finitely presented pushout
  (the expressions come from Generated).  spec-pullback: Spec T is the
  set of cocones to R.  No SQC.

SpecMaps.seg: 3.2.2, SQC part
  At.theorem: for FP A and presented K, Hom(K,A) -> (Spec A -> Spec K),
  phi |-> (x |-> x phi), is an equivalence (SQC for A).
  Maps.spec-pullback: Spec T = Spec A *_{Spec K} Spec B as the usual
  pullback (x, y, path in Spec K).
  Affine.exists: for FP A, B, K and ANY maps f : Spec A -> Spec K,
  g : Spec B -> Spec K, merely a finitely presented T with
  Spec T = Spec A *_{Spec K} Spec B.

Functions.seg
  Equivalences of function types: inverse, pre, post, uncurry, and
  2-out-of-3 (cancel).

SqcTensor.seg: 3.3.1
  At[A,B,T,c,ft,fb].theorem: for a coproduct T of A and B, with FP T and
  FP B, the map T -> (Spec A -> B), c |-> (phi |-> (phi (x) B)(c)), is an
  equivalence.  phi (x) B is the map T -> B induced by (iota_B phi, id).
  The proof is the paper's chain: SQC for T, Spec T = Spec A * Spec B,
  currying, SQC for B, with psi o (phi (x) B) = phi (x) psi (key).
  FP A is not needed beyond FP T.

Vanishing.seg: 3.3.2
  PolyCoproduct: A[X] (the coefficient quotient of polynomial/) is a
  coproduct of A and R[X].
  Eventually vanishing sequences: `polynomial` turns u with a mere bound
  into the unique x : R[X] with coefficients x = u (unique by
  coefficients-injective, hence no choice).
  Lemma[A,fa,s,ev].theorem: for FP A and s : Spec A -> (N -> R) with each
  s(x) eventually vanishing, merely N with s x n = 0 for all x and n >= N.
  3.3.1 with B = R[X] gives one polynomial p over A; x (x) R[X] acts on
  coefficients (coefficientwise); the length of a mere list for p bounds.
  Hypotheses: uniform SQC, FP A.

BoundedCorollary.seg: 3.3.3 by the paper's route
  s(x)(n) = 1 if n < f x, 0 otherwise; 3.3.2 bounds it; 1 != 0 gives
  f x <= N.  Hypotheses: uniform SQC (for A[X], R[X] and their tensor
  description), FP A, 1 != 0.
  Compare: ../presentations/UniformBounded.seg proves the same theorem
  with the same hypotheses (uniform SQC, FP A, 1 != 0) by a shorter
  route: SQC for A[T] and R[T] directly, no tensor product and no
  eventually vanishing sequences; ../bounded/Bounded.seg assumes only the
  two SQC instances (surjectivity for A[T], injectivity for R[T]) and
  1 != 0, for any R-algebra A.

Examples.seg
  R[X] (x) R[X] from two one-variable presentations; its spectrum is
  Spec R[X] * Spec R[X], and its presentation has two variables (refl).

Not done here: 3.3.4 (Loc, SQC, Z-choice), which needs D(f) = Spec A[1/f]
from Section 3.1 (worker A, ../affine).
