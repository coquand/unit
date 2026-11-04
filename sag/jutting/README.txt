The main theorem of L. S. van Benthem Jutting, "The development of a text
in AUT-QE" (preprint, Eindhoven; Symposium on APL, Paris, December 1973):
if f is bounded by n and injective on [1,n], then f is surjective on
[1,n].  Injection.seg follows his proof C (induction on n >= 1; in the
step, the cases f(n') = n' with his function a, and f(n') <= n with his
function b; his labels b1, b2, i, 1]-4] are kept).

Unit's naturals start at 0, so [1,n] is [0,n) here: the theorem is stated
for n = k+1, and Jutting's n' and n are the tops n and k of [0,n+1) and
[0,n).  Images are data (y with y < n and f y = x), constructed by the
proof; equality of naturals is decided where Jutting writes "if ... then".

Ring.seg and NatOrder.seg are plain copies from sag/gcddomain (naturals,
order).  Check (from unit/):   ./segc sag/jutting all
  2026-11-04: 4 modules, 0 failed, 0.01 s.   No Theory parameters (no univalence, no replacement).
