Univalence and replacement for axiomatic examples
================================================

Check from primrec:

    ./segc sag/replacement all

All work is isolated here.  Base.seg, Prelude.seg, Paths.seg, Axioms.seg and
FunExtUA.seg are dependencies read through relative symlinks to core.
Neither core/All.seg nor any sag file is modified by this development.

All.seg's Theory segment assumes:

    univ        : [l] Axioms[l].Univalence
    images      : [l] [k] Replacement[l,k].Images
    surjections : [l] [k] [j]
                    (Replacement[l,k].Surjectivity (images @l @k)) @j

The last two parameters together express ONE replacement axiom schema.
Images alone is not replacement.  Given A : U l, B : U k, small identity
types of B, and f : A -> B, images chooses I : U l and A -> I -> B, with
commuting triangle and embedding I -> B.  Surjections states that the
chosen A -> I induces an equivalence on sections of EVERY proposition
family over I, at every level j.  In particular I is independent of j.
The small-domain formulation uses a chosen small representative of a
U l-small type; no resizing or truncation is assumed in the axiom.

This follows cavrep.pdf, Definitions 2, 4 and 6.  The all-level schema is
split into data and its property because level-polymorphic types need not
belong to a universe in seg.  Like univalence in core, the axiom is an
explicit parameter, not a globally inhabited constant.  Funext is derived
from univalence by the existing FunExtUA proof.

Derived and checked:

* Truncation[l].Trunc[A]: the image of A -> Top, its propositionality,
  dependent induction at arbitrary levels, beta, and uniqueness.
* Completion[l].Complete[A,F]: the small image of F : A -> U l;
  the universe is locally small by univalence; the extended family is
  univalent and the quotient is surjective at arbitrary levels.
* Test.seg: empty truncation is empty, unit truncation is inhabited,
  elimination into U l+, and a completion base that stays in U l.

The beta rules are proved identities, not new evaluator reduction rules.
This is an axiomatic ambient development, not a proof of replacement in
the presheaf model; core/CTrunc remains an independent model construction.

To use this with the SAG development, its owner can import Replacement
and place the desired files in a segment with the three parameters above,
as in this All.seg.  Truncation and Completion are optional derived files
imported inside that segment.  Imports resolve in the entry point's own
directory; the corresponding files and core dependencies must be available
there (relative symlinks suffice).  The existing SAG proof files have been
left untouched for their owner to integrate when ready.  Loc, SQC and
Z-choice are separate mathematical hypotheses when a result requires them.
