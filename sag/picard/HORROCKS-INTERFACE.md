# Chart triviality: second A/B handoff

The first phase is complete: LaurentResults supplies the algebra for the
conditional Proposition 4.6. This phase must remove **ChartTriviality**.
Both are now proved: `HorrocksProof.Over[A,setA].horrocks` in `../horrocks/`,
and `ChartTriviality.Over[R,setR,sag].corollary-2-3` here.
The final result is `PicardComplete.Over[R,setR,sag].equivalence`.
The interface and original division of work below are retained for reference.

## Ownership and entry points

- **A owns `picard/`** and the interface files below. A constructs finite
  rank-one projectors from affine line bundles, relates their freeness
  certificates to bundle trivialisations, and proves Corollary 2.3.
- **B owns a new `horrocks/` directory**. B proves the polynomial theorem
  `HorrocksInterface[l].Over[A,setA].Horrocks`. This includes the passage
  from projector certificates to the ideal-divisor version in Appendix 1,
  if B uses that proof. B should link the interface files read-only.
- Shared libraries and the completed `laurent/` remain unchanged.

The authoritative types are in `RankOneProjector.seg` and
`HorrocksInterface.seg`. They use `Ring[l].CRing`, `Ring[l].Nat`,
`Presentations[l].Fin`, and the existing actual quotient ring
`PolynomialRing[l].Extension[A,setA].ring`.
The new files are imported by `picard/All.seg`.
Full direct check after the affine projector construction: **7,144
declarations, 0 failed, 2.61 s**, with nine expected negative tests.
An isolated export of all 201 source files gives the same result.
No new axioms or checker changes.

## Exact algebraic target

A rank-one projector consists of a finite square matrix E, with:

1. E² = E;
2. explicit coefficients witnessing that its entries generate the unit ideal;
3. every 2-by-2 minor zero.

A freeness certificate is a column x and row y with

    x_i y_j = E_ij,       Σ_i y_i x_i = 1.

A certificate after inverting f is a natural number N and vectors X,Y with

    X_i Y_j = f^N E_ij,   Σ_i Y_i X_i = f^N.

Both freeness statements are propositionally truncated. No assertion that
these equations are equivalent to abstract localised-module freeness is
being assumed: A must prove the geometric adapters it uses.

`ProjectorFreeness.seg` already checks the global certificate: for x,y
as above, r ↦ x r and v ↦ Σ y_i v_i are mutually inverse between A and
the fixed vectors of E. Both formulas preserve addition and scalar
multiplication. This proof needs no SAG axiom and no Horrocks hypothesis.
`Factors` writes 1·E rather than E in the matrix equation; the proof
explicitly removes that harmless factor.

Monic polynomials are represented by an arbitrary list of lower
coefficients followed by 1, in ascending coefficient order, then mapped
into the actual polynomial ring. This includes the constant monic
polynomial 1 and uses no decidable coefficient equality or actual-degree
operation.
`HorrocksInterface.leading` and `above` verify the leading coefficient
and vanishing of all higher coefficients.

**B's target:** a rank-one projector over A[X] with a certificate after
inverting such a monic polynomial merely has a freeness certificate.
The interface states this for a commutative set-valued ring A. Only A=R is
needed for Proposition 4.6. Any proposed weakening to a local/SAG base
should be recorded explicitly before changing the interface.

## A's checked affine projector construction

Steps 1–5 below now check. See [AFFINE-PROJECTOR.md](AFFINE-PROJECTOR.md)
for the precise theorem and implementation. The construction avoids the
general line-bundle/finitely-presented-module correspondence:

1. Associate an R-module line and its dual to an R×-torsor.
2. Use Z-choice to obtain a finite standard-open cover with frames.
3. Use 7.1.8 for the line and its dual to extend their local frames as
   fractions of global sections s_i and t_i.
4. The pairings r_i=t_i(s_i) are units on their respective opens. By SQC
   these are elements of A, and the existing standard-open certificate
   theorem supplies c_i with Σ c_i r_i=1.
5. The rank-one identity t_i(v)s_i=t_i(s_i)v gives the dual-basis identity
   v=Σ s_i(c_i t_i(v)). It supplies the finite projector.
The checked theorem packages a projector, an equivalence from global
sections to its fixed vectors, and preservation of addition and
A-scalar multiplication. B's interface is unchanged.

**Still assigned to A:** turn a trivialisation on D(f) into the displayed
power certificate, using fraction representations and a common
annihilating exponent; turn a global freeness certificate back into a
bundle trivialisation; finish the two-chart argument below.

## From monic triviality to the two charts

The charts remain lo(x)=[x:1] and hi(y)=[1:y].
Z-choice at zero on one chart gives g with g(0) a unit and a
trivialisation over D(g). Write

    g(X)=a0+a1 X+...+an X^n,     a0 invertible.

Use the monic polynomial

    f(X)=X (X^n+(a1/a0)X^(n-1)+...+an/a0).

On units, f(X)=a0^(-1) X^(n+1) g(1/X), so the opposite chart carries
D(f) into D(g). Horrocks gives a trivialisation of the whole opposite
chart; then repeat with the charts exchanged.
The normalization by a0 is necessary; the paper's displayed formula
suppresses it. A coefficient-list bound suffices in place of the actual
degree. Z-choice enters here and in the finite dual-basis construction.

## Appendix 1 cautions for B

The formal gcd branching and comaximal patching are substantial parts of
the proof, beyond the two lifting lemmas. Do not assume residual
discreteness or use excluded middle to perform this branching.
The global principal generator need not be monic over a disconnected
base. The footnote's idempotent condition should read e(1-e)=0.
The final interface asks for freeness, not a global monic generator.
