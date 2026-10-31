LARGE-FIELD DIAGONAL SEPARATOR
==============================

1. Checked endpoint

DiagonalSeparator.Over[k,setk,dec,nontrivial].At[
  S,D,cp,n,b,epsilon].theorem candidates distinct : Data

Inputs:
- k is a commutative set-ring with discrete field operations dec: each
  element is either zero or has an explicit inverse, and 1 is not zero.
- S and D are k-algebras; cp presents D as the algebra coproduct S tensor S.
- b is an actual TraceBasis of S of rank n.
- epsilon is an actual DiagonalCertificate.Witness in D: multiplication
  sends epsilon to 1, epsilon equalises the two copies of S, and epsilon
  is idempotent.
- candidates is a pairwise distinct scalar family of length
    suc(Integers.times (FiniteProduct.size n n) n),
  the explicit n^3+1 bound (including n=0).

Data contains actual scalar a, element z of S, inverse w of D, and

  (left(z) - right(z)) * w = 1 - epsilon.

It also retains the formula z = a H_b(a), with scalars interpreted in S.
H_b is the Kronecker coefficient list of the chosen basis, in the finite
index convention used by PolyRegular: the last basis index is the
constant coefficient. The equality is an inverse on the complementary
diagonal component; it does not assert that left(z)-right(z) is a unit
of all of D.

No factorisation, splitting algebra, discriminant, primitive-element
principle, choice of an off-diagonal basis, or unknown theorem parameter
occurs. The tensor basis, polynomial basis, determinant, degree bound,
nonzero scalar search and inverse are constructed from checked modules.
The result is actual data, not truncated existence. The inputs may be
consumed inside truncations in a larger theorem.

2. Proof, backwards from the required equation

An inverse u of epsilon+Delta(z) supplies w=(1-epsilon)u. The identities
of the diagonal idempotent imply Delta(z)w=1-epsilon.

On the full tensor algebra D form
  g(T) = epsilon + T H_Delta(b)(T).
The coefficients epsilon,Delta(b_i) are a regular family. Indeed expand
  epsilon = sum left(b_i) right(c_i),  sum b_i c_i = 1.
An element y annihilating all Delta(b_i) can replace left(b_i) by
right(b_i) after multiplication by y. Thus y epsilon=y. If y also
annihilates epsilon it vanishes.

PolyRegular's checked polynomial McCoy theorem makes g regular in D[T].
The constructed k-basis of D has rank r=n^2 and extends to a k[T]-basis
of D[T]. Multiplication by g is represented by an injective r by r
matrix. The checked square-matrix McCoy theorem makes its determinant
regular, hence nonzero in the nontrivial k[T]. Each matrix entry has
degree at most n. Following the existing exterior determinant operations
constructs an actual coefficient list of degree at most r*n for the
determinant. This does not assume a determinant expansion formula.

The checked polynomial root bound and finite zero search choose a
candidate a where the determinant is nonzero. Polynomial basis
coordinates commute with evaluation, so this determinant is exactly
the determinant of multiplication by g(a) on D. The adjugate constructs
an inverse of g(a). Finally g(a)=epsilon+Delta(a H_b(a)).

3. Reusable modules owned here

BoundedPolynomialDeterminant (35 declarations): actual raw coefficient
representatives with degree bounds, closed under exterior operations;
determinant of an n by n matrix of degree <=d has degree <=n*d.

SquareMatrixMcCoy (14): injective square matrix => regular determinant,
using the pre-existing rectangular McCoy theorem; rank zero allowed.

DiagonalRegularContent (35): regularity of epsilon and basis differences;
regularity of their Kronecker polynomial.

FiniteBasisRegularMatrix (20): regular multiplication gives an injective
matrix in an actual finite basis, over an arbitrary base ring.

BoundedPolynomialSearch (23): finite search for a nonzero value of a
nonzero polynomial on a sufficiently long distinct scalar family.

SeparatorCorner (19): inverse of epsilon+delta gives the complementary
inverse of delta; arbitrary commutative set-ring.

DiagonalPolynomialValue (37): the explicit element a H_b(a), equality
g(a)=epsilon+Delta(z), and the final complementary inverse.

PolynomialBasisSpecialisation (21): evaluation commutes with polynomial
basis coordinates and the multiplication determinant.

FinitePolynomialSelection (45): reusable theorem for every finite free
algebra S over a discrete field: a regular polynomial p of degree <=d
has a unit specialization on any n*d+1 distinct scalar family. Retains
an actual chosen index and scalar and an explicit inverse.

DiagonalSeparator (36): complete assembly of the endpoint in section 1.
SeparatorRegression (55): concrete checks described below.

Total: 340 new declarations in eleven owned modules. All other .seg files
are relative links. TensorFieldBasis, PolynomialBasis,
PolynomialBasisBounds, RightAdjugate and FiniteAlgebraDeterminantUnit
were constructed by the parallel basis agent and are reused unchanged.

4. Regression cases

- Full separator for F2 over itself: use its actual presentation,
  constructed tensor product and constructed diagonal certificate. The
  truncation is retained only for the constructed diagonal input; the
  separator is actual for each such input. The supplied scalars are 0,1.
- Polynomial p=T over F2: regularity comes from checked MonicRegular.
  The scalar search computes to 1 and the specialization is a unit.
- Rank-zero algebra over F2: the zero polynomial is regular in the zero
  algebra; the empty multiplication determinant is 1. The constructed
  inverse works without assuming that the target algebra is nonzero.
- Nontrivial complementary inverse in F2 x F2: epsilon=(1,0),
  delta=(0,1), epsilon+delta=1. The inverse produced on the complement
  is (0,1); delta has no global inverse.

Isolated copies under /tmp, leaving working files unchanged, rejected:
- changing the computed chosen scalar for p=T from 1 to 0;
- claiming delta*w=1 instead of 1-epsilon;
- claiming determinant degree <=d instead of <=n*d.
Each failed at the intended declaration, not at parsing or imports.

5. Validation

Fresh built checker, All.seg --opened:
  13,487 declarations, 0 failed, 6.21 seconds.
./segc sag/etale-field-diagonal-separator all:
  314 modules, 0 failed, 5.68 seconds.
Every one of the 340 new declarations is listed in
etale-field-diagonal-separator.opens. The complete --opens run reports
"nothing else opened" for all 340; 13,487 declarations, 0 failed,
6.53 seconds. Maximum per new declaration: 0.02 seconds, 40 distinct
opened definitions (the latter is the computed scalar regression).

The imports preserve the existing All.seg parameters for univalence,
replacement and surjections. No new axioms, shared-file edits, checker
changes or commits. The checking server is stopped on completion.

6. Scope

This directory proves scalar selection and the complementary inverse.
It does not prove that z generates S, construct the sufficiently long
scalar family, or assemble the finite-small-field alternative. Those
are separate integration steps. The supplied epsilon can be obtained
from formal unramifiedness by the existing DiagonalCertificate theorem;
that theorem is not duplicated here. The cubic bound is deliberately
generous and has not been optimised.
