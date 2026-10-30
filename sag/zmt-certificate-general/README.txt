Generic finite-coordinate certificate and dependence
===================================================

1. Completed scope

The generic dependence/certificate theorem is checked for every number of
homogeneous coordinates n>=3, written n=extra+3. Thus projective dimension
is extra+2. Nothing is committed. This directory owns 21 new source files
(1132 declarations); other files are unchanged relative links to the
completed syzygy, Cech, action and global-lift developments.

No shared file, checker, previous development or .git file was changed by
this track. No axiom, choice or resizing principle was added. All.seg has
only the existing univalence, replacement-images and surjection parameters.

This milestone proves generic ordinary dependence, not full ZMT, Rees
comparison, weighted dependence in arbitrary dimension, or base descent.

2. Final scalar theorem: exact input and conclusion

ScalarResolutionDependence.Over[K0,D,setD,cfn,extra].Input[a,d,g,hg].Seq[c,lift].dependence

Parameters:
  D : commutative ring, setD : isSet D.R, cfn : CFN[K0,D].
  extra : Ring.Nat; nvar = Ring.plus extra 3.
  a : finite rank; d : Fin a -> Base.Nat are nonnegative defining degrees.
  g_i : finite term lists in nvar variables, with coefficients in D.
  hg_i : HomShift 0 d_i g_i, i.e. every term exponent has degree d_i.
  c : Nat -> C^1_D(-1), actual finitely supported generic Laurent cochains.
  lift : for every j, merely u_j in product_i C^2_D(-1-d_i) with
                       delta c_j = sum_i g_i u_j,i.

There is NO supplied resolution, syzygy matrix, syzygy-generation theorem,
chart lifting theorem, primitive, finite top-coordinate module, Gamma
relation, or zero-reflection theorem among these hypotheses.

The conclusion merely contains a finite list qs of D-coefficients, with
N=len qs (N=0 allowed), and merely h and a_i such that

  c_N - sum_{i<N} q_i c_i = delta h + sum_j g_j a_j,

where h is an actual C^0_D(-1) cochain and a_j is an actual
C^1_D(-1-d_j) cochain. The list is stored head-last, as in the unchanged
CertifiedDependence theorem. Seq.Result and Input.Bdry are the precise
Unit types. Polynomial action remains visible in Bdry; no quotient
cohomology object is constructed.

GenericResolutionDependence exports the same theorem using the internal
rank-one family representing C^q(-1). ScalarResolutionDependence removes
that representation from the final inputs/output by the sole coordinate.

3. Count of stages and finite zigzag

F0=S(-1), F1=sum_i S(-1-d_i). For n=extra+3 coordinates, construct exactly
extra subsequent homogeneous kernel stages, through F_(n-2). Raising goes
from ordinary 1-cochains to top ordinary (n-1)-cochains:

  delta c = A0 u1,
  delta u1 = A1 u2,
  ...,
  delta u_(n-3) = A_(n-3) u_(n-2),

and records the finite top coefficients of u_(n-2). Cardinalities of the
indexing subsets are respectively 2,3,...,n. Therefore every intermediate
intersection, not just the full chart, needs the local exactness proved
here. For n=3 there are zero subsequent syzygy stages; for n=4 one; for
n=5 two. No positivity hypothesis is silently used at a small rank.

The Gamma relation is recursively nested truncation of these equations
and the terminal finite-coordinate equation. ZigzagCharacterisations
proves both directions of its familiar flattened forms at depths one and
two: dc=A u,top(u)=p; and dc=A u,du=H w,top(w)=p.

4. Construction and proof files

ChartDenominators
  For a subset s, bound the negative parts of all finitely many source
  exponents only on inverted coordinates; set L_i=0 on other coordinates.
  Proves the coordinatewise meaning of the chart support predicate,
  translation inverses, and preservation of the original chart under both
  translations. Forbidden exponents in an overlarge support list may have
  zero coefficient; they are not falsely assumed admissible.

PolynomialCoefficientParts, ChartPolynomialization,
LaurentPolynomialCoefficients, ClearingCoefficientBridge
  Characterise every tower grading projection on coefficients. Clear
  f(m) to f(m-L) in the polynomial tower, prove its homogeneous degree is
  k+deg L, and compare it at ALL Laurent exponents. Conversely extend
  tower coefficients by zero at negative coordinates, with explicit
  finite-support and homogeneous-degree witnesses.

TowerLaurentAction, PolynomialTowerProducts
  Prove one-variable monomial coefficient translation; iterate variables
  and sum terms. Thus mulP p (coeff x)=coeff(phi(p)*x). Derive compatibility
  of term-list products and finite sums with the constructed ring tower.
  Multiplication/action compatibility is proved, not an added hypothesis.

HomogeneousRepresentatives, LocalizedSyzygies
  Choose homogeneous term-list representatives by degree filtering under
  truncation. Clear a COMMON subset-supported denominator of a polynomial
  kernel vector, apply the constructed homogeneous polynomial kernel
  generation, and unshift. Prove the resulting Laurent action equation,
  chart vanishing, degree, and finite support for EVERY subset.
  The sibling GlobalCechSyzygies packages these finite local choices into
  actual shifted cochain-family lifts, setting wrong-cardinality entries
  to zero and uniting their finite supports.

FinitePolynomialResolution, HomogeneousStageRepresentatives
  Store finite homogeneous matrices and their proven identities. A
  cursor keeps its next target definitionally equal to its current source,
  extending the finite chain by zero modules/maps. The theorem used in
  the final proof is HomogeneousStageRepresentatives.constructed: it
  reuses HomogeneousStages.initial UNCHANGED, chooses homogeneous matrix
  representatives under truncation, and uses the named next-state equality
  to transport its tail. No resolution data escape truncation globally.

MatrixActionLaws, ResolutionCechDiagram, FiniteExactSchedule
  Ring matrix identities give zero composites on every Laurent chart.
  Polynomial matrix action commutes with the structural alternating Cech
  differential; d^2=0. This gives an actual generic double complex.
  FiniteExactSchedule constructs exactly the local exactness needed for
  its finite raising zigzag from the generated kernel stages.

CertificateExtension, FiniteZigzagCertificate, CechZigzagSchedule
  A descent step: from u=b p+H t, A H=0 and d a=A b, the correction
  c-a p is closed; contract it and obtain c=q h+a p. These SUBTRACTIONS
  are the alternating corrections of the downward zigzag. No contraction
  is commuted with multiplication by a polynomial. Iterate this checked
  relation-certificate extension; closure under D-linear combinations is
  constructed at each step. Terminal coordinates zero imply zero residual,
  hence a primitive by the explicit top contraction. Earlier primitives
  are supplied by the below-top contraction, justified by strict natural
  cardinality inequalities. Raising partners remain under truncation.
  Apply unchanged CertifiedDependence to this constructed relation.

GenericResolutionDependence, ScalarResolutionDependence
  Build the required finite polynomial resolution, actual exactness and
  contraction/top schedule. Eliminate its truncation into the final result.
  Named sum-comparison and scalar-evaluation lemmas expose the final
  original sequence identity with no columns or resolution input.

5. Orientation and common exponent interfaces

Ordinary exponents: Presentations.Fin n -> Base.Nat.
Laurent exponents:  Presentations.Fin n -> ZInt.Int.
The new coordinate is inr tt; old coordinates are inl i.
The generic Cech subset order puts the NEW coordinate FIRST, with
structural differential d(a,b)=(d a,a-d b). All dd, commutation, raising and
reflection equations use this orientation. No dimension-specific sign table
or comparison with the old fixed-four-coordinate sign convention is assumed.

6. Regression and mutation checks

GenericCertificateRegression checks:
  - final dependence over every CFN D with empty generators and with a zero
    generator assigned degree five, in n=3,4,5;
  - actual three/four-coordinate Gamma characterisations, both directions;
  - n=5 (P^4), input (X^3,Y^3), TWO CONSTRUCTED syzygy stages and final
    dependence, including a direct scalar-cochain instance;
  - the cubic P^4 and empty-input cases specialised to Z.

The n=5 sequence instance is the actual zero sequence with its original
lift, while the same file also exports final dependence for EVERY sequence
with the original mere lifts. No hand-written syzygy matrix is used.

Two mutations were rejected, then restored and rechecked:
  - replacing correction c-a p by c+a p rejects closedness and reconstruction;
  - replacing raised degree k+deg L by k-deg L rejects clearing homogeneity
    and the inverse degree proof.

7. Validation / reproducible commands

From CANONICITY:
  timeout 55 ./unit/segc unit/sag/zmt-certificate-general all

For a fresh process, from this directory, SEG is the built executable
reported by `cabal list-bin exe:seg` from unit:
  timeout 55 "$SEG" All.seg
  timeout 55 "$SEG" All.seg --opened
  timeout 55 "$SEG" All.seg --opens zmt-certificate-general.opens

Fresh All.seg: 9371 declarations, 0 failed, 4.45 s.
Full server: 169 modules, 0 failed, 4.17 s.
All 1132 declarations owned by this directory are covered by the complete
measured opening inventory: every --opens report says "nothing else opened".
Max new-declaration profile: 43 distinct definitions opened, 0.07 s.
The spec is a measured inventory, not a separately derived minimal whitelist.
It includes expected ring/quotient/tower aliases, cursor/module/tuple fields,
finite sums and degree projections. Four chart-sign proofs open the local
GenericSupport.bad/badStep helper; its full stable internal identifier
(#2366) is explicitly recorded, since --opened displays only its short name.
See VALIDATION.txt for module counts and baseline checks.

8. Exact limits and next work

Scope is n>=3 homogeneous coordinates, indexed n=extra+3. No projective
assertion is made for n=0. The special n=1,2 dependence statements are NOT
part of this theorem; they require separate small-rank treatment. In
particular this proof uses below-top contraction of F0 at subset cardinality
2, which is appropriate precisely for n>=3. It does not incorrectly assume
that cardinality 2 is below top at n=2. The separate observation that O(-1)
has no all-negative top monomials in n>=2 is not needed for the present scope.

The ordinary total grading and nonnegative defining/syzygy shifts are used.
Zero columns are retained, top coordinate boxes can be generous, and no
minimality, canonical resolution or terminating resolution is asserted.

This integrates generic syzygies with generic Cech certificates and ordinary
dependence. Rees comparison/evaluated vanishing, weighted generic dependence,
full ZMT, and arbitrary-base descent are separate milestones. There is no
claim that the present theorem by itself is the final ZMT statement.
