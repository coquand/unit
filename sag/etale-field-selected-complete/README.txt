COMPLETE SELECTED SEPARABLE MONOGENIC FACTOR
==========================================

1. Exact checked theorem

SelectedFactorComplete.Over[k,setk].At[
  S,input,reduced,D,cp,epsilon].theorem
  : SelectedFactorStatement.Over[k,setk].At[S].Result input

The input record is the existing SelectedFactorStatement.Input:
- discrete nontrivial field operations on k;
- an actual finite k-basis of S;
- an invertible trace-pairing determinant;
- a selected decidable prime of S.
The additional arguments are reducedness (a*a=0 implies a=0), an actual
algebra coproduct D=S tensor_k S, and its DiagonalCertificate.Witness.

The conclusion is exactly the existing proposition, merely a selected
idempotent e outside the prime, a generator z, a monic polynomial P,
a derivative inverse on eS, and polynomial representations of each
of the finitely many basis vectors:

  e^2=e,  e not in q,
  e P(z)=0,
  e(P'(z)*v-1)=0,
  e(b_i-Q_i(z))=0 for every basis vector b_i.

The derivative is the established dual-number Horner convention.
The theorem does not assume monic annihilators, a finite coefficient
subfield, a sufficiently large scalar list, a separator, or a primitive
element. All of those intermediate data are constructed when required.

2. Proof

FiniteMonicCoefficientFamily uses the finite basis and the checked
determinant trick to construct a monic annihilator of every basis
vector, merely. Finite choice is used only inside this truncation.
CoefficientCollection supplies one finite family containing all lower
coefficients, together with explicit locations of their occurrences.

Given such finite data, FiniteCoefficientField performs bounded closure
under the field operations. With stopping bound n^3, it returns either:
- n^3+1 distinct scalars; or
- an actual finite coefficient subfield containing every coefficient.
This is a constructive finite disjunction; infinitude or finiteness of
the whole field is not decided or assumed.

In the large branch, DiagonalSeparator constructs z and w with
  Delta(z)*w=1-epsilon.
SeparatorSelectedFactor then constructs the selected generator and its
selected separable equation, intersecting the resulting idempotents.

In the small branch, FiniteMonicCoefficientFamily.Given.Lift constructs
actual monic lists over the finite subfield and proves their roots in
the restricted algebra. SmallFieldBranch constructs the finite image
subalgebra, its selected finite field, and a primitive element using the
proved finite-field theorem. The polynomial identities are transported
through the nonunital inclusion of the selected corner.

Both branches return the same existing truncated result. The outer
monic-equation truncation therefore eliminates directly into it.

3. Files and integration

Owned:
- SelectedFactorComplete.seg: 31 declarations, the complete assembly.
- SelectedCompleteRegression.seg: 44 declarations.
- All.seg, README.txt, etale-field-selected-complete.opens.

All other .seg files are relative links to existing developments.
There are no new mathematical axioms or shared/checker modifications.
The inherited All.seg uses the same univalence, replacement and
surjection parameters as its dependencies. Nothing is committed.

Import ordering matters: NormalFormModuleBasis has a local alias Span,
whereas the finite-field arithmetic tree imports a global module Span.
All.seg imports the selected-generator modules before that arithmetic
tree. This avoids the no-shadowing collision without modifying any
shared file. Consumers should preserve that ordering.

4. Regressions

F2 over itself runs the actual theorem, with its actual finite basis,
trace pairing, zero prime, presented tensor product and constructed
diagonal certificate. No selected factor or annihilator is supplied to
this full theorem regression.

Separate branch regressions use T+1 for the basis vector 1:
- the bounded closure at bound 1 computes to the large branch;
- both explicit constructor branches feed the complete assembly;
- lifting to the identity finite subfield preserves the coefficient 1
  and the root equation by computation;
- at bound 8 the same actual closure computes to the small branch, and
  the resulting actual subfield feeds the lifting and small-field
  construction. The impossible large case is eliminated by the checked
  root bound applied to T^2+T, whose roots include all of F2.

Two mutations in isolated /tmp copies were rejected at the intended
regression declarations: changing the computed large-branch tag to the
small tag, and changing the lifted coefficient 1 to 0. Working files
were never mutated.

5. Validation

Fresh All.seg --opened:
  14,818 declarations, 0 failed, 7.62 seconds.
./segc sag/etale-field-selected-complete all:
  348 modules, 0 failed, 6.81 seconds.
All 75 owned declarations are listed in etale-field-selected-complete.opens;
all report "nothing else opened". Full --opens run: 14,818 declarations,
0 failed, 7.14 seconds. Every owned declaration takes at most 0.01 s.
The computed small-branch regression opens at most 41 definitions.
The checking server is stopped on completion.

6. What this theorem assumes and what remains outside this directory

An actual finite basis, reducedness, perfect trace and a diagonal
certificate are inputs here. Existing unramified-field theorems construct
these from finite presentation and formal unramifiedness; their final
wrapper is separate integration work. The selected prime is explicit
and decidable, as in the existing SelectedFactorStatement interface.

This is the field-level selected-factor theorem. It does not perform the
coefficient-and-denominator bridge to the arbitrary local base, construct
that base's residue field, or assert the final local etale theorem.
