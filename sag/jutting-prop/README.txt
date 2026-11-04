Jutting's theorem (an injection of [1,n] into itself is a surjection), as in
sag/jutting, but with "x is an n-image under f" a PROPOSITION: the
propositional truncation of the type of witnesses (y with y < n and
f y = x).  Each use of the induction hypothesis gives a witness only
merely; it may be taken because the goal, an image, is a proposition
(take).  Otherwise the proof is the same (Jutting's proof C).

The truncation is Truncation.seg (from sag/gcddomain), built from the
replacement parameters images/surjections of the Theory segment, which also
has univalence (univ).  The proof uses only the truncation: univalence is a
parameter but is not used.

Check (from unit/):   ./segc sag/jutting-prop all
  2026-11-04: 8 modules, 0 failed, 0.01 s.
