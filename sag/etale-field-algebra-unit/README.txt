A unit determinant gives a unit in a finite free algebra
=======================================================
FiniteAlgebraDeterminantUnit.Over[k,setk,S,n,basis].At[x] uses the matrix
  matrix j i = basis.coordinate (x * basis.vector j) i
with the existing column,row convention and ExteriorModel determinant.
from-unit takes a unit witness for this determinant and constructs a unit
witness for x. from-nonzero additionally accepts the discrete-field
zero-or-unit decision and nonvanishing of the determinant.

RightAdjugate constructs the right adjugate from the existing left-adjugate
identity for the transpose and the proved determinant-transpose identity.
It solves multiplication by x on the coordinate vector of 1. Reconstruction
then gives an explicit inverse in S. No cancellation of determinants is
used. The unit-determinant theorem works over every commutative set-ring,
and the rank-zero case is included.

Regression: multiplication by 3 in Z/4Z with the rank-one base basis;
the determinant and the constructed inverse both compute to 3.
Two isolated mutations were rejected: omission of the adjugate transpose,
and the false claim that this computed inverse is 1.
Validation: fresh All.seg 8090 declarations, 0 failed, 3.59 s;
segc all 191 modules, 0 failed, 3.15 s. There are 54 owned declarations,
48 named; all 48 have clean --opens audits. Each owned declaration takes
at most 0.01 s and opens at most 31 definitions.

There are no new axioms, checker changes or shared-source edits. Reused
source is linked relatively. Nothing was committed. This helper does not
choose x or show that a determinant polynomial has a nonzero value.
