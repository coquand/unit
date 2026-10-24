# Completion update — 2026-10-20

`PicardComplete[l].Over[R,setR,sag].equivalence` now proves Proposition 4.6
from SAG alone. `ChartTriviality.Over[R,setR,sag].corollary-2-3` discharges
the former chart hypothesis using the completed Horrocks theorem.
The checked algebra and Horrocks interface types are unchanged.
See `README.txt` and `CHECKED.txt` for the final check and compatibility copies.
The design and earlier milestones below are retained as history.

# Proposition 4.6: shared interface for terminals A and B

The next phase, removing chart triviality, has its handoff in
[HORROCKS-INTERFACE.md](HORROCKS-INTERFACE.md).

**B has supplied all three fields, and the integrated theorem checks.**
The authoritative types are in [PicardInterface.seg](PicardInterface.seg).
The detailed handoff is [HANDOFF-B.txt](HANDOFF-B.txt).

## Ownership

- **A owns `picard/`**, including this interface, the unit group, the two-chart projective line, `Line`, the twists, and the classification.
- **B owns `laurent/`**, all polynomial/Laurent representations, their algebra, and their connection to uniform SQC.
- Link shared files read-only; do not edit the other terminal's source files. Record any proposed interface amendment for A before relying on it.
- Existing libraries are unchanged. All dependency links in `picard/` are relative.

## Common types

The base is `Ring[l].CRing` with an explicit proof `setR`.
`PicardUnits[l].Over[R,setR]` supplies:

- `Unit = (x : R.R) * RL[R].unit x`;
- `one`, `times`, `inverse`, and powers indexed by `Ring[l].Nat`;
- `group`, in the existing `Torsor.Ab` format.

`PicardInterface[l].Degree` has constructors `nonneg n` and `negative n`;
these denote n and -(n+1), respectively, with n in `Ring[l].Nat`.
`PicardDegree.seg` proves setness; B need not prove it again.

## B's checked deliverables

Instantiate `PicardInterface[l].Over[R,setR].AlgebraResults` from the
common SAG assumptions. Its three fields are:

1. **`factorisation : Factorisation`**. Every `t : Unit -> Unit` merely
   has d, u, a, b with a,b : R.R -> Unit such that, for every unit x,
   `t x = u * x^d * a(x) * b(x^-1)`.
2. **`degree-unique : DegreeUnique`**. If
   `x^d * a(x) = x^e * b(x^-1)` for every unit x, then d=e.
3. **`intersection : ChartIntersection`**. If f,g : R.R -> R.R agree
   as `f(x)=g(x^-1)` on units, then both are constant with value f(0).

The exact parenthesisation, quantifiers and truncations are in the SEG file.
These are module parameter types, not postulates or additional global axioms.

**Representation choice for B's review:** the interface uses units of
function algebras: `PolynomialUnit = R.R -> Unit` and
`LaurentUnit = Unit -> Unit`. B derives their polynomial/Laurent meaning
from uniform SQC. This avoids exposing a coefficient representation to A.
Evaluation of a polynomial unit at zero is already `at-zero` in the
interface. The underlying coefficient-comparison lemmas stay with B;
A consumes their `ChartIntersection` and `DegreeUnique` consequences.

B owns any required adapters from the old `projective/PolynomialFunctions`
and `LaurentFunctions`. A has ported the short chart quotient to the common
ring in `Projective.seg` (a link to `projective/`) and the constancy argument in
`PicardConstant.seg`; A needs no separate conversion to `Algebra.CRing`.
There is not yet a comparison equivalence to the old ring-record version
of P1; the port uses the same chart relation and quotient construction.

## Chart and sign conventions

- `lo(x) = [x:1]`, `hi(y) = [1:y]`; the overlap is xy=1.
- The frames of O(d) satisfy **e_hi = x^d . e_lo** after transporting
  the hi frame to lo(x).
- Equivalently, `coordinate_lo = x^d * coordinate_hi`.
- `PicardTwists.Glue.transition` checks this equation on actual frames.

## Geometric hypothesis

`PicardTwists[l].Over[R,setR].ChartTriviality` states that for every
B : P1 -> Line there is a mere trivialisation of each whole chart:

    || (x:R) -> B(lo x) = trivial ||
      * || (y:R) -> B(hi y) = trivial ||

It does not merely assert pointwise triviality. This remains the one
intended geometric hypothesis after integration of A and B. Its proof,
through the affine line-bundle/module correspondence and rank-one Horrocks,
belongs to the next phase.

## A's completed conditional theorem

`PicardTheorem[l].Over[R,setR,algebra,charts].proposition-4-6` is checked,
where `algebra : PicardInterface.Over[R,setR].AlgebraResults` and
`charts : PicardTwists.Over[R,setR].ChartTriviality`.

There are no further geometric or algebraic parameters:

- `PicardExistence.seg` derives mere classification by O(d) from
  `algebra.factorisation` and `charts`.
- `PicardSeparation.seg` derives separation of twists from
  `algebra.degree-unique`, using the gauge equation extracted from an
  actual bundle isomorphism.
- `PicardClassification.seg` uses these and `algebra.intersection` to
  prove the equivalence with inverse B -> (B([0:1]), degree B).

`PicardTwists.seg` constructs O(d) from cocycles on the fibres of the
chart cover using the existing torsor construction. No quotient elimination
into a 1-type is assumed. `PicardSetDescent.seg` proves the dependent
set-valued gluing used for equivariant maps.

B supplied `LaurentResults[l].Over[R,setR,sag].results`.
`PicardSAG[l].Over[R,setR,sag,charts]` now instantiates the final theorem.
`PicardSAG.FromLocSQC` exposes the stronger formulation without Z-choice.
None of the shared interface types changed.

Full direct check of `picard/All.seg`: **4039 declarations, 0 failed,
1.35 s**, with seven expected negative tests. An isolated export of all
129 reachable source files as regular files also checks: **4039 declarations,
0 failed, 1.53 s**. No trusted-only checking or new postulates.

The nested `Tensor` module of `torsor/TorSum.seg` is named `TensorMaps`,
because the combined entry point also imports SAG's `Tensor` file.
