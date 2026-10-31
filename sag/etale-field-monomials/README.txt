Normalized multivariable monomial expansions
==========================================

1. Scope and assumptions

Every Presentations.Expr on Fin n is expanded into an actual finite family
of coefficient/exponent pairs. Equal exponent vectors are combined and
zero coefficients are removed. Every surviving coefficient is nonzero,
and the exponent map is injective. Evaluation agrees with the original
expression in every algebra over the coefficient ring.

The coefficient ring is any commutative set-ring A with decidable zero
membership. It need not be a field or a domain. Exponents and arities use
Ring.Nat. The construction uses finite lists and decidable tests; there
is no choice of representatives and no truncation in the output.

The structural relation additionally requires 1 != 0. It constructs the
nonempty normalized family for X_last^N - X_last^(N+1) P directly, rather
than trying to infer polynomial nonzeroness from its value at a point.

2. Main interfaces

MonomialEvaluation[l].Over[B].monomial n x u
  u : Presentations.Fin n -> Ring.Nat.
  At zero variables the value is 1. At suc n it is the last-variable
  power times the monomial on the first n variables. zero-value,
  unit-value and product prove its basic semantic laws.

MonomialFamily[l].Over[A,setA,n].Normalized[zero-dec].expand e
  : SparseData[e]

The record SparseData[e] has fields:
  size : Ring.Nat;
  coefficient : Fin size -> A.R;
  exponent : Fin size -> (Fin n -> Ring.Nat);
  nonzero i : coefficient i != 0;
  distinct i j : exponent i = exponent j -> i = j;
  value B x : eval e = sum_j iota(coefficient j) * monomial n x (exponent j).

Here zero-dec a is either a=0 or a!=0. The finite sum is exactly
FiniteIdeal.Sums[B.ring].sum, with its newest-index-first convention.
The family may be empty, as it must be for the zero polynomial.

MonomialDifference[l].Over[A,setA,n,zero-dec,one-nonzero].At[N,e,p]
  p : MonomialFamily.Over[A,setA,suc n].Normalized[zero-dec].SparseData[e]

exports expression, sparse : SparseData[expression], distinguished,
leading-coefficient and leading-exponent. The expression is
  X_last^N + (-1)*(X_last^(N+1)*e).
The size is suc p.size. The distinguished newest index has coefficient 1
and exponent (0,...,0,N); every old index has coefficient -p.coefficient i
and exponent (old coordinates, N+1+p.exponent i last). Shift injectivity
preserves distinctness; the last-coordinate inequality separates the
new term from every old term. Eval[B,x].expression-value and sum-value
both identify the value with x_last^N - x_last^(N+1)*eval e.

3. Files and proof

MonomialExponents.seg: exponent vectors, equality decision, addition and
unit vectors.
MonomialEvaluation.seg: recursive monomial semantics and product law.
MonomialLists.seg: raw expression expansion, list multiplication and
semantic correctness in every algebra.
MonomialNormalize.seg: insertion combines equal exponents, then a second
pass removes zeros; both passes preserve evaluation.
MonomialFamily.seg: enumerate a list by Fin(length) and package the
nonzero/injective/evaluation properties in SparseData.
MonomialDifference.seg: direct normalized nonempty relation for the
zero-dimensionality-to-finiteness construction.
MonomialRegression.seg: computational and semantic examples over Z/4.

These are the seven owned proof files. All other proof files are reused
through relative links; All.seg is a local import harness. No shared or
checker file was modified. No new axioms were introduced. The harness
retains the existing univalence, replacement and surjection parameters.
Nothing is committed.

4. Validation

Fresh built checker, All.seg --opened:
  7314 declarations, 0 failed, 2.75 seconds.
./segc sag/etale-field-monomials all:
  169 modules, 0 failed, 2.41 seconds.

There are 238 owned declarations. Every one is covered by
etale-field-monomials.opens; all 238 report "nothing else opened".
Each owned declaration rounds to 0.00 seconds in the fresh run. Generic
proofs open at most 11 distinct definitions. Concrete normalization
regressions open at most 46, intentionally computing the list operations,
exponent equality decisions and Z/4 arithmetic tables.

Regressions check:
- (X+Y)^2 has three terms and mixed coefficient 2 with exponent (1,1);
- its evaluation at (2,1) is 1 and satisfies the semantic theorem;
- X+3X normalizes to the empty family;
- (2X)(2Y) normalizes to the empty family, exercising zero divisors;
- the zero-variable expression 1+3 normalizes to the empty family;
- N=0 and P=0 gives the one-term structural relation 1;
- N=1 and P=X+Y has the required negative coefficients, distinguished
  degree 1, shifted last degree 3, and evaluation 2 at (2,1).

Two deliberate mutations were rejected and restored: the shifted
coefficient was stated as +1 instead of -1 over Z/4, and the shifted last
degree was stated as 2 instead of 3. The restored regression rechecks.

5. Limits and downstream work

This is an expansion theorem, not a quotient construction or a packaged
polynomial ring equivalence. The output is duplicate-free but is not
sorted into a chosen monomial order. No uniqueness theorem comparing two
arbitrary normalized families is asserted.

The nonempty relation does not itself prove that its evaluation is zero;
the caller supplies zero-dimensionality and the expression representing
its witness. Nagata substitution, integrality and finite-dimensionality
are separate developments. The helper does not assume any of them.

Checking from unit/:
  ./segc sag/etale-field-monomials all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg sag/etale-field-monomials/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg sag/etale-field-monomials/All.seg --opens sag/etale-field-monomials/etale-field-monomials.opens
