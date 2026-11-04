Gauss's lemma and "A gcd domain => A[X] gcd domain", as a reading example
(2026-11-03, for a test with Aarne Ranta).

Informal text, one section per file, every declaration of the seven
algebra files named:  doc/gcddomain.tex (.pdf)

Trimmed copy of sag/gcd (plain copies, not links, so the example is
frozen).  Changes with respect to sag/gcd:
 * Coefficients.seg (new): the coefficient lemmas on A[X], extracted
   unchanged from exterior/CharPoly.seg (the only part of CharPoly that
   PolyBase used); PolyBase's CP now refers to it.
 * cong2 moved into Prelude.seg; Presentations is no longer used.
 These drop the exterior-algebra/determinant/SIP chain: 40 -> 23 files.

Check (from unit/):   ./segc sag/gcddomain all
  2026-11-03: 24 modules, 0 failed, 0.12 s.

No new axioms; rests on the Theory parameters univ (univalence) and
images/surjections (replacement), used for A[X] as a quotient and for
function extensionality.
