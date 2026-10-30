Generic finite-variable homogeneous syzygies
==========================================

1. Status and scope

Checked, uncommitted development in this directory only. No shared source,
checker, earlier development or .git file is edited. Dependencies are relative
links to the existing weighted4/syzygies4/artin-rees developments. No new axiom,
choice or resizing principle is introduced. All.seg has exactly the existing
univalence, replacement-images and surjection parameters used by weighted4.

The main result is CONSTRUCTED finite homogeneous kernel generators for an
arbitrary finite homogeneous polynomial MATRIX, followed by finite iteration.
The number t of polynomial variables, both matrix ranks, and the requested
number of subsequent stages are arbitrary finite natural numbers. None is
fixed to four. This does not prove that a resolution terminates.

2. Main theorem (all hypotheses)

HomogeneousKernel.Tower[K0,A,setA,cfn,t].Input[a,r,d,c,m,hm].generators

Here:
  A is a commutative set-ring; cfn : CFN[K0,A].
  S = CoefficientPolynomial.CoefficientTower[A,setA].D t
    is A[X_1]...[X_t]. Its grading and CFN structure are CONSTRUCTED in the
    earlier CoefficientPolynomial file (HilbertCFN.poly at each successor).
  a, r : Ring.Nat are the source and target ranks.
  d : Fin a -> Base.Nat and c : Fin r -> Base.Nat are nonnegative shifts.
  m : Fin a -> (Fin r -> S.R) lists the a columns of an r-row matrix.
  hm i j : Hom(d_i-c_j, m_i,j), with differences interpreted in Z.

The result merely contains Data, with fields available through M.Witness[w]:
  rank        : Nat
  shifts      : Fin rank -> Base.Nat
  columns     : Fin rank -> (Fin a -> S.R)
  homogeneous : Hom(shifts_j-d_i, columns_j,i)
  identity    : m columns_j = 0 for every j
  generate    : for every y with m y=0, merely z with H z=y
  lift        : for EVERY INTEGER n and every homogeneous kernel vector
                y_i of degree n-d_i, merely z_j of degree n-shifts_j
                with H z=y.

Generation witnesses and generator matrices are under propositional
truncation. No matrix, generation theorem, degree bound, or term-list
representative is an extra hypothesis of this theorem. Input m is retained.
Empty source/target ranks, zero polynomials and negative coordinate degrees
are allowed. Source and target shifts themselves are nonnegative.

The intermediate abstract theorem M.Of[coh,pieces].homogeneous requires only
coherence of S and finite nonnegative homogeneous decompositions. The public
Tower.Input theorem constructs both hypotheses from the CFN base and t.

3. Prescribed finite initial resolutions

HomogeneousStages.Tower[K0,A,setA,cfn,t].initial n state
  : Trunc[Initial n state]

A State contains exactly a homogeneous input matrix with its two ranks and
nonnegative shifts. Initial 0 state is Top. Initial (n+1) state contains the
FULL kernel Data for state together with Initial n for the resulting matrix
H. Hence every stage retains its differential identity, ordinary kernel
generation, and all-integer homogeneous lifts; it is not a sequence of
matrices with exactness left as an assumption. This gives ANY prescribed
finite number of initial homogeneous syzygy stages, under truncation. It
asserts neither a terminating resolution nor an upper bound on its length.

4. Proof organisation

FiniteHomogeneousPieces:
  Every element of the generic polynomial tower merely has a finite list of
  homogeneous summands with nonnegative natural degrees. Induct on t; at a
  successor, use Horner recursion on a coefficient-list representative.
  Constants preserve old pieces and multiplication by the new variable
  raises each degree by one. Representatives are chosen only under truncation.

ShiftedParts:
  Bound the shifted degree of each of these summands by a finite sum B.
  The interval 0,...,B is indexed without repetitions. An individual
  homogeneous summand is selected exactly once. Additivity reconstructs each
  original entry from its shifted projections. sub-shift proves the common
  integer-shift cancellation used in homogeneous matrix multiplication.

HomogeneousKernel:
  FreeCoherent supplies finite ordinary kernel generators over S. Finitely
  many truncated choices supply homogeneous summand lists of their entries.
  A common bound B supplies columns (old generator k, degree e=0,...,B).
  Column entry i is pr_(e-d_i)(h_k,i). Matrix multiplication commutes with
  shifted degree projection, so every new column is a kernel vector.
  The reconstruction lemma proves these columns generate the whole ordinary
  kernel. Projecting ANY ordinary generation equation for a homogeneous
  input supplies coefficients of degree n-e_j. This works for every n in Z,
  without homogeneity assumptions on the original coefficients.

HomogeneousStages:
  Recursion on the prescribed length; eliminate each constructed kernel
  matrix into the truncated statement about the remaining finite tail.

5. Ordinary exponent/coefficient bridge

FiniteExponents.Exp t = Presentations.Fin t -> Base.Nat.
The newest variable is inr tt and the old variables are inl i. This is the
CoefficientTower recursion order and matches the sibling generic Cech
track's coordinate split. No dependency on that track is used. degree is the
sum of the coordinates (newest plus recursively old). Equality of exponents
is decidable; no equality test on coefficients is used.

PolynomialTowerBridge.Over[A,setA] proves:
  Coeff t x v             recursive ordinary coefficient extraction
  ext                     these coefficients determine x
  term, phi               scalar monomials and finite term lists into S
  cf                      independently defined term-list coefficient function
                          (sum of equality-selected coefficients)
  coeff-phi               Coeff(phi ps)=cf ps
  phi-eq, cf-eq           equality of coefficient functions iff equality in S
  rep                     every S element merely has a term-list representative
  Support.finite          every S element merely has finite coefficient support
  Supported.represent    every coefficient function with a finite support list
                          is represented in S, using nub of that list; each
                          exponent is counted once even if support repeats.

PolynomialDegreeBridge proves that scalar monomials have their total
exponent degree, and that filtering any term list by any integer total
degree computes its tower grading projection. The coefficient comparison is
Filter.coefficient. Negative degrees are included.

6. Regressions

GenericSyzygyRegression, over every CFN A and specialised to Z:
  (X^3,Y^3), (X^3+Y^3,Y^3), (X,X), the empty source row, and zero of degree 5;
  the actual 2-row, 3-column matrix with columns (X,0),(Y,X),(0,Y);
  two successive stages of that matrix (HomogeneousStages.initial 2);
  a zero-rank target;
  application of CONSTRUCTED lift to the nonzero kernel vector (-1,1) of
  (X,X), and to a zero vector with negative shifted coordinate degrees.

PolynomialBridgeRegression:
  cubic exponent/degree/coefficient in two variables;
  zero variables;
  repeated support [u,u], with represented coefficient at u proved equal to
  ONE, rather than the multiplicity two; this is also instantiated over Z.

Two deliberate mutations were rejected, then restored:
  replacing (-1,1) by (1,1): syz-hom and syz-zero fail;
  assigning degree 1 to the cubic input: h-cubic/h-nonmonomial fail.

7. Validation and commands

From CANONICITY (each invocation bounded by 55 seconds):
  timeout 55 ./unit/segc unit/sag/zmt-syzygies-general all

For a fresh process, from this directory, let SEG be the existing built
unit executable (obtain it with `cd unit` then `cabal list-bin exe:seg`):
  timeout 55 "$SEG" All.seg
  timeout 55 "$SEG" All.seg --opened
  timeout 55 "$SEG" All.seg --opens zmt-syzygies-general.opens

Fresh All.seg: 7167 declarations, 0 failed (534 new versus weighted4's 6633).
--opened: at most 34 distinct definitions opened by a new declaration;
maximum new-declaration time in the recorded run is 0.02 seconds.
--opens: all 534 new declarations covered; each says "nothing else opened".
The spec is a complete measured inventory, not an independently derived
minimal whitelist. The declared openings include the tower/ring/quotient
aliases needed to compare quotient polynomial operations and explicit
finite sums/degree projections. These aliases are inherited unchanged.
See VALIDATION.txt for the final fresh/server/baseline run counts.

8. Limits / next integration work

No ring equivalence or term-list multiplication compatibility is packaged.
The proved polynomial bridge gives the explicit maps, coefficient equality,
extensionality, finite supports and representatives. Multiplication and
module operations in the kernel theorem use the constructed ring S itself.

The main theorem permits arbitrary finite variable and matrix counts, but
uses the ordinary total grading and nonnegative source/target shifts.
It does not give a multigraded or arbitrary-signed-shift statement.

Columns in the constructed matrix are intentionally generous; zero columns
are retained. There is no canonical or minimal generating matrix.

The imported tree still includes old four-coordinate developments. The
new generic proof reuses only their variable-independent arithmetic,
finite sums, finite choice and range/selection utilities (plus generic
coherence and polynomial-tower libraries). It does not invoke a fixed-four
syzygy theorem, dependence theorem or Cech theorem to prove generic kernels.
A later library cleanup can extract these utilities without changing the
proof. No such cleanup was made in shared files.

This does not integrate these matrices with the new generic Laurent/Cech
complex, supply its sign comparison with the old four-coordinate complex,
prove arbitrary-dimensional dependence, Rees comparison, arbitrary-base
descent or full ZMT. Those remain separate tracks. The present construction
provides the homogeneous finite initial resolutions those tracks require.
