Constructive Gaussian quotient coordinates
=========================================

1. Normal forms (checked)

GaussianQuotient.Over[A,dec].normal-form n m v

A is a commutative ring with a specified zero-or-unit operation dec.
v : Fin m -> (Fin n -> A.R) is the finite family of relations.
The returned NormalForm[n,m,v] supplies an actual rank r, linear maps
project : A^n -> A^r and section : A^r -> A^n, with:
  project(section x) = x;
  project(v_j) = 0;
  x - section(project x) is an explicit combination of the original v_j.
No truncation, subspace oracle, or assumed basis occurs in this algorithm.

Induct on n. If all last coordinates of the relations vanish, recursively
process the lower n-1 coordinates and retain the last free coordinate.
Otherwise choose a relation with invertible last coordinate and its
inverse w; let u=w*v_p, so u_last=1. Reduce x to
  lower(x) - x_last*lower(u).
Recurse on the reduced relations without deleting any relation indices.
The inclusion of lower coordinates is a section of reduction. The
remaining difference is x_last*u plus the lifted lower difference. Both
are explicit combinations of the original relations, using the span
operations in GaussianVectors. This avoids a large expanded coefficient
identity and preserves the intended inductive proof structure.

2. Actual quotient bases (checked)

GaussianModuleQuotient.Over[A,setA,dec].At
  [n,m,v,M,phi,onto,relations,kernel]

M is a Modules.Over[A,setA].Module. phi is a linear map from
DescentLinear.Free n to M; onto merely gives a preimage for each element.
relations says phi(v_j)=0. kernel merely supplies a span witness in v for
each vector killed by phi. The output includes:
  rank, vector, coordinate, add, scale, on-vector, expands;
  basis : DescentLinear.On[M].Basis rank vector;
  frame : DescentLinear.On[M].Frame rank.

Two representatives with the same image have the same Gaussian projection.
Consequently the pair (projected coordinates, reconstruction equation) is
a proposition. The mere surjectivity witness is eliminated into this
proposition to construct coordinates, with no choice of representatives.
The output is an actual finite basis, not just a finite spanning family.

GaussianAlgebraBasis.Over[A,setA,dec,B].At
  [n,m,v,phi,onto,relations,kernel].basis
packages this in the exact TraceBasis.Over[A,setA,B].Basis[Q.rank] record.
The source data describe the underlying module of B. This is the adapter
for the separate finite-unramified trace-pairing theorem.

3. Files and validation

Six owned .seg files: GaussianVectors, GaussianLinear, GaussianQuotient,
GaussianModuleQuotient, GaussianAlgebraBasis, GaussianRegression.
All other .seg files are unchanged relative links. No new axioms,
checker edits, shared edits, or commits. All.seg inherits the usual
univalence, replacement and surjection parameters.

  ./segc sag/etale-field-gaussian all

Fresh checks, 31 October 2026:
  All.seg: 7458 declarations, 0 failed, 2.92 s.
  segc all: 171 modules, 0 failed, 2.54 s.
  253 owned declarations, all covered by etale-field-gaussian.opens.
  Each owned declaration takes at most 0.01 s and opens at most 36
  definitions (the largest opening lists are concrete F2 computations).

F2 regressions compute the rank and selected projected values for:
  zero-dimensional empty input;
  three-dimensional space with no relations;
  a zero relation;
  duplicate relations (1,1), (1,1);
  full rank from the two standard basis vectors;
  the chain (1,1,0), (0,1,1), with quotient rank one.
The actual quotient map F2^2 -> F2, (a,b) |-> a+b, is supplied with
surjectivity and its diagonal kernel generator; the module adapter
constructs its basis and reconstruction theorem.

Two mutations were rejected: using zero as the normalized pivot and
claiming the chain quotient has rank two. Both were restored and checked.

4. Scope

This completes the finite-matrix quotient basis dependency. It does not
yet construct the finite free bounded-monomial source and its finite
relation matrix from an arbitrary finite algebra presentation. That
assembly belongs to the separate finiteness development.
