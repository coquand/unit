Proposition 4.6 of projective.pdf: complete
==========================================

Final entry point:
  PicardComplete[l].Over[R,setR,sag].equivalence
    : Equiv (Line * Degree) (P1 -> Line)

The forward map is (a,d) |-> (p |-> a tensor O(d)(p)). Its inverse is
B |-> (B([0:1]), degree B), with both inverse equations checked.
Line is the small type of R^*-torsors. P1 is the two-chart quotient.

Assumptions
-----------
Univalence and replacement (with the existing all-level surjectivity
schema), and SAG's Loc, uniform SQC and Z-choice. No additional algebraic
or chart-triviality hypothesis, no postulates and no checker changes.

The previous conditional interfaces remain available:
  PicardSAG.Over[R,setR,sag,charts]
  PicardSAG.FromLocSQC[R,setR,sqc,loc,charts]
The latter avoids Z-choice but takes chart triviality as a hypothesis.
PicardComplete discharges that hypothesis through ChartTriviality.

New geometric bridge
--------------------
AffineLineProjector constructs a finite rank-one projector over a finitely
presented affine algebra, with fixed vectors equivalent to global sections.
The completion adds eleven files (545 lines):

LineFrameRecovery: a line vector with a normalised functional determines a
unique torsor frame. Mere inhabitation is used only for a proposition.
AffineFreeFrames: a global projector factorisation gives a global frame.
AffineScalarFactor: any line/dual pair factors the projector up to a scalar.
AffineScalarClearing: equality on D(f) is killed by a power of f, via 7.1.8.
AffineLocalFrames: extend a local frame and its dual by 7.1.8. Their pairing
agrees with a power of f on D(f). Clear this ONE scalar difference to obtain
exactly HorrocksInterface's local certificate.
MonicLineTriviality: Horrocks now proves triviality over Spec R[X] from a
frame on a monic standard open (the torsor form of Proposition 2.2).
AffineLineCoordinate: Spec R[X] is R, compatibly with polynomial evaluation.
ReciprocalMonic: reverse and normalise a polynomial with invertible constant
coefficient, and multiply by X, obtaining a monic open in the other chart.
LineFrameNearZero: Z-choice supplies a polynomial neighbourhood of zero
with a frame. No choice of an actual polynomial degree is needed.
ChartTriviality: apply monic triviality to the opposite chart, in both
directions. corollary-2-3 has the interface type; paper-corollary-2-3 states
mere constancy at the respective chart origins, as in the paper.
PicardComplete: combine the proved charts with the proved Laurent algebra.

All truncations of frames are OUTSIDE the whole space of sections.
Pointwise mere triviality is not substituted for a chart trivialisation.

Horrocks integration
-------------------
../horrocks/ contains the completed COLL/horrocks-review proof, followed by
three experiments: a named Cleared record, truncation combinators, and an
external proof-producing ring normaliser. The original review package is
unchanged; current package hashes are in ../horrocks/SOURCES.sha256.
See ../horrocks/PROOF-TOOLS.txt for the new generator and regression tests.
HorrocksProof.Over[A,setA].horrocks uses no SAG axioms and applies to any
commutative set-valued ring A.

The combined namespace has no private copies: every shared file is a link.
Name clashes are resolved at the source (horrocks' nested Vanish modules
are VanishingResult, torsor/TorSum's nested Tensor is TensorMaps, and
laurent uses closed/LocalizationKernel).

Conventions
-----------
lo(x)=[x:1]; hi(y)=[1:y]; overlap xy=1.
e_hi = x^d . e_lo after transport from hi(x^-1) to lo(x).
Degree nonneg(n) denotes n; negative(n) denotes -(n+1).
The older projective/Algebra.CRing implementation is not used: the short
chart quotient is ported to the common Ring.CRing. An explicit comparison
with that older implementation is not part of this package.

Verification
------------
  python3 check.py
  python3 check.py --isolated
An alternative executable can be supplied with --checker PATH.
The script checks the full source closure, without --only. An isolated
export contains regular copies of every reachable source and a hash manifest.

Latest isolated check, with the local-global Horrocks (2026-10-21): 280
sources, 10614 declarations, 0 failed, 5.01 s. Ten expected negative tests.
All 280 imported modules check individually; GeneratedRing takes 0.24 s.
Regression tests check eighteen generated identities and reject both false
input identities and a deliberately corrupted generated proof. See CHECKED.txt.


P^n and Section 7 of projective.pdf (Theorem 7.3: line bundles on P^n,
n >= 2, are Line x Z) build on this directory: see ../pn/README.txt.
