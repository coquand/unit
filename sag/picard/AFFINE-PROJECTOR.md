# Affine line bundles represented by finite rank-one projectors

The checked entry point is

    AffineLineProjector[l].Over[R,setR,axioms].At[Alg,fp,T].theorem

Here `Alg` is an R-algebra, `fp` proves finite presentability, and
`T : Spec Alg -> (R×-torsors)`. The assumptions are the existing SAG
bundle: Loc, SQC and Z-choice, over univalence and replacement.

The theorem merely supplies a natural number n, a rank-one projector E
over Alg, and an equivalence

    global sections of the associated line ≃ {v : Alg^n | Ev=v}.

The witness includes preservation of addition and scalar multiplication
by Alg. The projector has all four fields of the checked Horrocks
interface: its entries, idempotence, explicit coefficients generating
the unit ideal, and vanishing 2-by-2 minors.

`LineProjectorExamples.SmallLine.represented` instantiates this for the
actual small `PicardLines.Line` families used in Proposition 4.6.
There is no additional projectivity or local-triviality hypothesis.

## Construction

`LineAssociated.seg` constructs the associated module as functions on a
torsor satisfying

    v(a·t) = a⁻¹ v(t).

Ordinary-weight functions `d(a·t)=a d(t)` form the associated dual.
Operations are pointwise. Choosing t gives a linear equivalence with R
by evaluation at t; its inverse uses the torsor difference. The existing
module structure-identity theorem identifies the module with the regular
module. Weak quasi-coherence is a proposition, so mere inhabitation of
the torsor suffices to transfer it from R.

`LinePairing.seg` constructs ⟨d,v⟩: the function t ↦ d(t)v(t) is constant,
and unique choice gives its value without choosing a torsor point.
It proves linearity, normalised frame/dual-frame pairing, the rank-one
identity, and the exchange identity giving the 2-by-2 minors. The frame
of a·t is a times the frame of t, verifying the inverse-weight convention.

`AffineLineData.seg` uses Z-choice for a finite standard-open cover with
frames. The checked 7.1.8 extends each frame and dual frame as a fraction
of global sections s_i,d_i. Their pairings r_i are units on the original
opens: evaluation at the local torsor point gives explicit inverses for
the two numerator values.

SQC identifies r_i with elements of Alg. The standard-open cover theorem
gives coefficients c_i with Σ c_i r_i=1. Replacing d_i by c_i d_i gives
normalised global data with Σ ⟨d_i,s_i⟩=1.

`RankOneTrace.seg` proves that a matrix with vanishing 2-by-2 minors and
trace one is idempotent, and provides the unit-ideal coefficients.
`AffineLineProjector.seg` applies this to E_ij=⟨d_i,s_j⟩, using SQC to
obtain entries in Alg.

The equivalence is explicit. Its forward map takes a section v to its
coordinates ⟨d_i,v⟩; its inverse sends a fixed vector a to Σ a_i s_i.
The rank-one identity and the normalisation prove both inverse equations.
`ModuleFiniteSums.seg` provides the small finite-sum lemmas used here.

## Checks and remaining work

The seven new files total 548 lines. The full direct check and the isolated
export both report **7,144 declarations, 0 failed, 2.61 s**. Nine negative
tests are expected, including two new tests rejecting a dropped frame
weight and treating the zero section as a basis.

The export is `/private/tmp/picard-affine-export-ivo6jkw6`: 201 regular
source files, with their source paths and SHA-256 digests in `manifest.json`.

Dependencies are linked read-only. There is one `LocalizationKernel`
(closed/), used by the Laurent and Section 7 trees alike.

Completion update: all those adapters now check in `AffineLocalFrames`,
`AffineFreeFrames` and `ChartTriviality`. The scalar-factor shortcut clears
only one scalar difference after extending a local frame and its dual.
B's completed Horrocks theorem is integrated in `../horrocks/`.
`PicardComplete.Over[R,setR,sag].equivalence` has no chart hypothesis.
See README and CHECKED for the current 9773-declaration isolated check.
No shared interface type changed. Nothing is committed.
