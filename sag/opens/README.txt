SAG Section 4.2: open subtypes, and Proposition 2.2.3(b),(c)
============================================================

Worker B's development. Check from the repository root:
  ./segc sag/opens all
Independent check:  (cd sag/opens && "$(cabal list-bin exe:seg)" All.seg)

Dependencies are read-only symlinks: closed/ClosedProp.seg (worker A's
shared definition of closed propositions) and everything of Sections 2-3
(affine/, tensor/, presentations/). Foundation: univalence and
replacement. Loc, SQC and Z-choice are explicit parameters; where all
three are needed they come as SAGAxioms.Assumptions.

OpenProp.seg: 4.2.1
  Units n xs = || (i : Fin n) * unit(xs i) ||.
  Witness Q = (n : Nat) * (xs : Fin n -> R) * Equiv Q (Units n xs);
  Open Q = || Witness Q ||; OpenSubtype X S = (x : X) -> Open (S x).
  The same shape as ClosedProp (Zeros replaced by Units). No axioms.

Units23.seg: 2.2.3(b),(c)  (Loc, SQC)
  nonzero-iff-some-unit: not (all x_i = 0) iff merely some x_i is a unit.
  R/(x_1,..,x_n) has no points, so it collapses (2.2.2); its kernel
  certificate gives 1 = sum x_i c_i; Loc finds a unit summand.
  nilpotent-iff: x nilpotent iff not not (x = 0), by 3.1.8 at A = R
  and 2.2.3(a). Only 1 != 0 is used from Loc here.

OpenOps.seg: 4.2.2-4.2.4
  open-empty, open-top, open-or (append the lists), open-and (all
  products x_i*y_j), preimage: no axioms.
  SAG.open-neg-closed / neg-closed-open (4.2.2) and SAG.stable (4.2.3(e),
  double-negation stability): Loc, SQC, through 2.2.3(b).
  Binary intersections and unions with empty and true give the finite ones.

Separation.seg: 4.2.5, 4.2.6  (Loc, SQC)
  open-ne: for affine X, x != y is open. A presentation embeds Spec A in
  R^n; x != y says the vector of coordinate differences is nonzero.
  4.2.6: x specialises to y (every open containing x contains y) iff
  not not (x = y).

Pad.seg
  Padding a list of length <= b with zeros to length b keeps "some entry
  is a unit" (1 != 0).

OpenAffine.seg: 4.2.7  (Loc, SQC, Z-choice)
  At[A,fp,S,o].theorem: an open subtype S of Spec A is affine-open.
  The paper's proof: Z-choice gives open witnesses on a cover D(f_i); on
  D(f_i) = Spec A_{f_i} their lengths are bounded (3.3.3, UniformBounded);
  padding and SQC for A_{f_i} give g_ij in A_{f_i}; then Glue.
  Glue: if V is covered by D(f_1..f_k) and affine-open on each
  Spec A_{f_i}, then V is affine-open. It uses 3.1.7 in the form
  OpenTransitivity.Localized.transitivity, finite choice, and
  concatenation of the k lists.
  affine-open-open: affine-open subtypes are open.

Transitivity.seg: 4.2.8 (affine case), 4.2.9, 4.2.11
  Affine[..].theorem: in Spec A, an open subtype of an open subtype is
  open (4.2.7 twice and Glue). Loc, SQC, Z-choice.
  sigma (4.2.9(a)): the case A = R: open propositions are closed under
  dependent sums. transitivity (4.2.9(b)): pointwise, for every type X;
  this includes 4.2.8 for schemes, without defining schemes.
  Implication (4.2.11): for P closed and Q open, (P -> Q) iff
  || not P + Q ||. The paper lists no axioms, but its proof uses 2.2.3(b);
  here Loc and SQC are parameters.

Not formalised: Remark 4.2.10 (dominance) is a remark.
