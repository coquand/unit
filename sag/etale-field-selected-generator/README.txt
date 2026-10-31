From a tensor separator to the exact selected field certificate
==============================================================

SeparatorSelectedFactor.Over[k,setk,field,S,n,basis,reduced,perfect,q]
  .Separator[D,cp,epsilon,z,w,inverse].theorem

returns merely SelectedFactorStatement.Selected[n,basis,q]. The inputs
include an actual tensor coproduct D, its diagonal certificate epsilon,
and the equation Delta(z)*w=1-epsilon. No minimal polynomial, relative
basis, coordinate identity or polynomial representative is assumed.
The specified prime is proper, has propositional membership and is
decidable, as recorded by PrimeIdempotents.Prime.

SeparatorSelectedGenerator constructs the minimal quotient Q=k[T]/(f)
of z, with its injection into S. Q is regular. Pulling the given prime
back to Q and applying SelectedFiniteAlgebraBasis constructs a basis of
one selected factor of S over the corresponding factor of Q.
TensorRelativeCoordinates gives the coordinate identities. The checked
MonicCoordinateGeneration construction then refines the idempotent and
produces an actual polynomial representative of every element of S on
that factor. The generator remains exactly z; the quotient-generator
identification is transported explicitly.

SeparatorSelectedFactor independently constructs a selected simple-root
monic equation for z, using SelectedSeparableAnnihilator. Multiplying
the two idempotents preserves the specified prime, generation, the root
equation and the inverse-derivative equation. This gives the exact
Selected result, with only the finite basis representations retained.

The separator search is a separate checked theorem in
etale-field-diagonal-separator. Its large/small coefficient-field
assembly is etale-field-selected-complete. The original fp+Unique
field hypotheses suffice in etale-field-complete.

Regression and validation

SeparatorSelectedRegression runs the full theorem on F2, at z=0 and
z=1, using the constructed presented tensor, original diagonal (under
truncation) and perfect trace. No selected factor is supplied. An
additional explicit F2 x F2 regression tests the factor intersection:
it keeps the first component and kills the second.

Fresh All.seg --opened: 11165 declarations, 0 failed, 5.37 seconds.
./segc sag/etale-field-selected-generator all: 266 modules, 0 failed,
4.86 seconds. Three owned files contain 124 declarations including six
open directives. All 118 named declarations are covered by
etale-field-selected-generator.opens, with nothing else opened.
Maximum per owned declaration: 0.03 seconds, 39 opened definitions.
Replacing the product of idempotents by their sum in an isolated copy
was rejected in four declarations, including the idempotence proof.

No new axioms, shared-source edits, checker edits or commits. Reused
modules are relative links. All.seg retains the existing univalence,
replacement and surjection parameters. This directory's theorem is
conditional on the explicit separator; the complete field theorem
constructs it and all other algebraic inputs.
