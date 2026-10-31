Finite coefficient subalgebra and selected finite field
=====================================================

1. Checked ambient-field interface

CoefficientSubalgebra.Over[k,setk,field,t,coefficients,K0]
  .At[S,d,basis].Generators[n,x,lower,roots]

Inputs:
  k is a discrete nonzero field (SelectedFactorStatement.Field);
  K0 is the ACTUAL finite Subfield record from FiniteCoefficientField;
  S is a k-algebra with an actual finite TraceBasis;
  x is any finite n-tuple in S;
  lower_i is a coefficient list over K0;
  roots says x_i satisfies the corresponding monic equation over K0.

The construction works for any finite n, including 0; n=2 is the intended
small-field primitive-element application. The coefficient lists and
monic equations remain explicit inputs, not a claimed primitive-element
existence theorem.

The result's Image.B is GeneratedSubalgebra over K0: its carrier is a
subtype of S, with membership the propositional truncation of expression
representations. It exports an injective ring map to S and the specified
generators. The result also gives size, enumeration, enumeration-injective,
and ACTUAL covers(b)=(i, enumeration(i)=b).

Equality in S is constructed from the supplied k-basis, using the checked
DiscreteCoordinates theorem. There is no extra equality-decision or
module-kernel hypothesis in this ambient-field interface.

2. Explicit finite construction

MonicFiniteImage.Over[R,setR,m,values,cover].At
  [S,equalS,n,x,lower,roots]
is the more general core, with an explicitly finite coefficient ring R
and a supplied equality decision in S.

Monic roots lift into the generated image by its subtype equality.
IteratedMonicBasis constructs the actual finite-free monic cover Q and
its map onto the image. Onto is proved using the image's expression
representatives and the universal map's generator equations.

FiniteTuples enumerates every coordinate tuple over the finite coefficient
ring, with actual coverage. FiniteFreeEnumeration expands these tuples
in the Q-basis. Mapping into the image gives a finite enumeration with
mere coverage. FiniteDedup removes repetitions using ambient equality.
Membership in the retained injective enumeration has a UNIQUE index;
therefore the mere representatives can be eliminated into that proposition
to obtain ACTUAL coverage. No global choice is used.

MonicFiniteImage also separately exports finite-data/finite as module
spanning data over R. It uses the images of Q's finite basis. The finite
set enumeration is not silently treated as a module basis.

3. Selected finite field

Adding reducedS (a*a=0 implies a=0) and a specified decidable proper prime
q of S, the ambient wrapper exports:

  .Selected[reducedS,q].theorem

This merely supplies a FinitePrimeFactor.Result for the image algebra.
The underlying complete construction is SelectedFiniteImage.Over[...].
For each result r, its Chosen[r] module constructs the selected field.

Reducedness is inherited by subtype equality. Regular witnesses are
constructed INSIDE the coefficient image: its finite module span gives
monic annihilators by FiniteSpanIntegral's determinant trick, and
ReducedIntegralRegular turns them into a=a^2*b with b in the image.
The specified prime restricts directly to a decidable proper prime there.
FinitePrimeFactor then supplies the annihilator idempotent.

Chosen[r] exports:
  field, set, field-decide, field-nonzero;
  exact finite size, injective enumeration and ACTUAL covers;
  projection: B0 -> field, a unital ring map;
  coefficient-map: R -> field and coefficient-injective;
  idempotent in S, square and outside the original q;
  to-ambient: field -> S, injective and preserving + and *;
  generator(i), with ambient image idempotent*x_i.

The field's unit maps to the idempotent. The inclusion into S is correctly
NOT asserted to be a unital ring map unless that idempotent equals 1.
The selected-field enumeration is deduplicated again after projection,
so its size is its actual cardinality.

4. Regression

FiniteSubalgebraRegression starts with S=F2 x F2, its actual two-vector
basis, and the first-projection prime (reusing the checked concrete ring).
K0 is constructed by the bounded coefficient-field algorithm. The two
complementary idempotents satisfy X^2-X over K0. The full finite-image
and selected-field constructions run. For every selected result, the
second generator is zero in the field and the first is nonzero.

Separate computations check four binary coordinate tuples and removal
of the duplicate from the list (1,0,1). Two isolated mutations were
rejected: replacing X^2-X by X^2, and claiming the deduplicated list has
three entries. Working files were never mutated.

5. Validation and scope

See the validation figures below. Eight owned proof/regression modules:
  FiniteTuples, FiniteDedup, FiniteFreeEnumeration, MonicValueNaturality,
  MonicFiniteImage, SelectedFiniteImage, CoefficientSubalgebra,
  FiniteSubalgebraRegression.
All other .seg files are unchanged relative links. No new axioms,
checker changes, shared edits or commits. The usual existing univalence,
replacement and surjection parameters are retained in All.seg.

What remains outside this directory: constructing the required separable
monic annihilators from the ambient field-theoretic data; multiplicative
cyclicity/Frobenius in the selected finite field; and extracting/lifting
the final primitive-element certificate. This directory supplies the
finite coefficient algebra and selected finite field once the displayed
monic equations are given. It does not assert full primitive existence.

Checked 31 October 2026:
  ./segc sag/etale-field-finite-subalgebra all
  243 modules, 0 failed, 3.77 s.
Fresh built checker: 10059 declarations, 0 failed, 4.29 s.
277 owned declarations including 16 open instructions; all 261 named
ones are covered by etale-field-finite-subalgebra.opens and report
"nothing else opened". Maximum per declaration: 0.02 s and 65 distinct
definitions opened (the long opening lists are concrete regressions).
The checking server is stopped.
