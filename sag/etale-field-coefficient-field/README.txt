Bounded coefficient-field dichotomy
==================================

1. Checked theorem and exact API

FiniteCoefficientField.Over[k,setk,decide,nonzero,t,coefficients].theorem M

Inputs:
  k is a commutative set-ring;
  decide(a) either proves a=0 or supplies w with a*w=1;
  nonzero proves 1 is not 0;
  coefficients : Presentations.Fin t -> k.R;
  M : Nat.

Output is an ACTUAL sum (not merely):
  Ring[l+].Plus (Closure.Distinct (suc M)) Subfield.

The first branch has an injective map Fin(M+1)->k: more than M pairwise
distinct field elements.

The second branch constructs a Subfield record with:
  ring, set;
  inclusion : RingHom.Hom ring k, and injective;
  field-decide : each element is zero or has an explicit inverse;
  field-nonzero : 1 differs from 0;
  size, enumeration : Fin size -> ring.R;
  enumeration-injective;
  cover(a) : an actual index i with enumeration(i)=a;
  coefficient(i) : a preimage in the subfield of coefficients(i);
  coefficient-image : inclusion(coefficient(i))=coefficients(i).

Thus size is the cardinality of the returned field, not a bound arising
from an enumeration with repetitions. Its carrier is literally a subtype
of k. There is no hypothesis deciding whether k itself is finite.

2. Simplified bounded algorithm

Source motivation: Lombardi--Quitte, Commutative Algebra: Constructive
Methods, LQ.pdf VI-1.9, pages 307-308. The proof seeks enough base-field
elements or a finite field containing the polynomial coefficients.

We use a simpler closure test for exactly that conclusion. The ambient
discrete field supplies a total inverse operation, assigning 0 at 0.
Start with the empty distinct list. Scan, in order:
  0, 1, every supplied coefficient;
  the negatives and total inverses of every list entry;
  the sums and products of every pair of list entries.

Every scan is finite and uses decidable equality. If a candidate is
missing, append that ONE element, retaining an injectivity proof. If
none is missing, all field operations preserve the finite list. After
M+1 failed tests there are M+1 distinct elements; otherwise closure has
already returned a finite coefficient field. No unbounded search,
choice, or decision of the ambient field's cardinality occurs.

Closing under total inverse directly is the deliberate simplification:
we do not first close only under addition/multiplication and then prove
finite injective multiplication is surjective. The required finite-field
conclusion has explicit inverses from the ambient field operation.

3. Modules

FiniteDistinct: decidable lookup, unique membership index for a distinct
list, and append-one preserving injectivity.

FiniteScan: finite dependent search, retaining the concrete failure.

DiscreteFieldOperations: equality decision from the field law and a
total inverse with the proved inverse equation at every nonzero element.

BoundedFiniteClosure: the generic bounded algorithm on a discrete type
with the listed operations. No ring laws are used in its termination.
Its run fuel n starts with n distinct entries and, if it never closes,
adds exactly fuel new entries. growth-zero proves the final cardinality.

FiniteCoefficientField: the closed list becomes a subtype of k with
propositional membership. Its ring laws follow by injectivity of the
inclusion, and its inverse operation is the restricted total inverse.
The finite indices and coefficient witnesses are retained explicitly.
The public theorem packages the finite subfield or the large list.

4. Regressions and validation (31 October 2026)

CoefficientFieldRegression runs the actual algorithm over F2 with
repeated coefficients (1,0,1). It computes:
  bound 1: the large branch, with distinct entries 0,1;
  bound 2: the small branch, with subfield cardinality 2.
It checks coefficient lifting, the returned field decision and actual
finite coverage, the empty coefficient case, and total inverse at 0,1.

Two isolated mutations were rejected: returning 0 as every inverse,
and claiming the second large-branch entry is 0. Working files were
never modified for these tests.

  ./segc sag/etale-field-coefficient-field all

36 modules, 0 failed, 0.09 s.
Fresh built checker: 1028 declarations, 0 failed, 0.17 s.
The six owned modules contain 192 declarations including 11 open
instructions; all 181 named declarations are covered by
etale-field-coefficient-field.opens and report "nothing else opened".
Maximum per declaration: 0.01 s and 45 distinct definitions opened
(the large lists are concrete computation regressions).

All other .seg files are unchanged relative links. No new axioms,
checker changes, shared edits or commits. The usual existing univalence,
replacement and surjection parameters are retained in All.seg.
The checking server is stopped.

5. Scope

This completes the bounded coefficient-field alternative required by
the small-field primitive-element branch. It does not construct the
coefficient algebra k0[x,z], a selected factor, a multiplicative-group
generator, or a primitive element; those remain downstream tasks.

No minimality theorem is asserted for the returned coefficient field,
and no separate numerical upper-bound theorem is packaged for its size.
Neither is needed for the displayed dichotomy or its finite enumeration.
