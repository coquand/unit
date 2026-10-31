Finite free unramified algebras have invertible trace pairing
===========================================================

1. Checked result

FiniteUnramifiedTrace.Over[R,setR].At[S,n,b].theorem fp unique proves

  unit(det( j,i |-> Tr(b_j b_i) )).

Here R is any commutative set-ring, S is an R-algebra, b is an explicit
finite R-basis of length n, fp is Presentations.FP S, and unique is
FormallyEtale.Unique S.  No field, standard presentation, lifting
existence, tensor-coordinate hypothesis or trace certificate is assumed.
The case n=0 is allowed.

At.duality fp unique additionally gives, merely, the actual family c_j
as a TraceDuality.Certificate.  Given this certificate, the named results
TraceDuality.Given.trace-identity, matrix-inverse, gram-determinant-unit
and nondegenerate prove

  a = sum_j iota(Tr(a b_j)) c_j,
  coordinates(c_j) * Gram = identity,
  det(Gram) is a unit,
  [all Tr(a b_j)=0] implies a=0.

All finite presentations, diagonal witnesses and their coefficient data
are eliminated only into propositions or kept inside truncation.
The existing All.seg univalence, replacement and surjection parameters
are reused; there are no new axioms, checker changes or shared edits.
Nothing is committed.

2. Basis interface

TraceBasis.Over[R,setR,S].Basis[n] has:
  vector : Fin n -> S;
  coordinate : S -> Fin n -> R;
  add and scale : R-linearity of each coordinate;
  reconstruction : sum_j iota(coordinate(a,j))*vector(j)=a;
  on-vector : coordinate(vector(j),i)=delta(i,j).

This is a genuine basis, not only a spanning family.  The Gaussian
development's GaussianAlgebraBasis produces exactly this record.
TraceBasis.At.trace is the sum of the diagonal coordinates of
multiplication.  product-coordinate, trace-add, trace-scale and
trace-index are proved.  The last is the decisive index calculation
sum_i lambda_i((a b_i)b_j)=Tr(a b_j).

3. Constructed scalar extension and tensor coordinates

FiniteVectorLinear proves linear extensionality on coordinate unit
vectors, both for vector targets and for an algebra target.

FiniteBasisScalarExtension builds a commutative B-algebra on B^n from
the structure constants lambda_i(b_j b_k) mapped R -> B.  Multiplication
is proved bilinear.  Its identities on pure S-vectors follow from the
basis reconstruction; linear extensionality reduces associativity,
commutativity and the unit law to those vectors.  The ring structure
and maps S -> B^n <- B are constructed, not postulated.

FiniteBasisEvaluation constructs the ring map from this coordinate
algebra to every common R-algebra target of S and B:
  v |-> sum_j f(b_j) g(v_j).
Preservation of multiplication again reduces to pure basis vectors.

TensorBasisConstruct sets B=S and uses the actual algebra-coproduct
universal property to map D=S tensor_R S into the coordinate algebra.
Evaluation maps back to D; the composite is the identity by agreement
on both S-factors.  Thus additive/right-S-linear coordinates on D and
their reconstruction are proved.  This discharges the intermediate
TensorBasis interface of DiagonalTraceBridge completely.

DiagonalTraceBridge applies these coordinates to the actual averaging
element constructed in etale-field-diagonal.  Its normalisation and
equalisation give the coordinate certificate.  TraceDuality proves the
trace identity, then applies coordinates to get the matrix inverse.
Determinant multiplicativity gives the unit witness.

4. Validation

Fresh All.seg: 7635 declarations, 0 failed, 2.86 s.
Nine owned proof modules contain 318 new declarations, including
18 open directives.  All 300 named owned declarations are covered by
etale-field-trace.opens.  The full server run passes 177 modules.
Every new declaration took at most 0.06 s and opened at most 18 distinct
definitions.  Allowed qualified openings include vector/map records,
finite sums, and concrete algebra/quotient carrier aliases; the complete
specification records these explicitly.

Regressions:
  - the full theorem for the rank-one base algebra over every R;
  - its actual constructed tensor coordinates and reconstruction;
  - the nonreduced base Z/4Z, including Tr(2)=2;
  - the rank-zero basis of the zero algebra, trace identity and determinant.

Two isolated mutations were rejected without modifying working files:
  - the wrong index in the trace-index identity;
  - replacing the multiplication structure constant by an addition one.

Commands, from unit/:
  ./segc sag/etale-field-trace all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-trace/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-trace/All.seg \
    --opens sag/etale-field-trace/etale-field-trace.opens

5. Remaining field work

This development does not construct a finite basis from finite algebra
presentation and zero-dimensionality.  It consumes an actual basis;
GaussianAlgebraBasis is one adapter to that interface.  The primitive
element theorem, selected-prime splitting and the residual denominator
bridge remain separate.  No unconditional completion of the field case
or flat-plus-unramified theorem is claimed here.
