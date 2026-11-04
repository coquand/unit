Gauss's lemma and "A gcd domain => A[X] gcd domain", with MERELY existing
gcds: a gcd domain gives  || GcdOf a b ||  for all a, b (no gcd function),
and the theorem gives the same for A[X].

Copy of sag/gcddomain (the reading example, informal text
doc/gcddomain.tex), changed in five files:
 * GcdDomain.seg: the field gcd is || GcdOf a b ||.  In a discrete domain
   || a | b || gives a | b (for a /= 0 the quotient is unique; for a = 0,
   || 0 | b || gives the proposition b = 0), so a gcd may be taken whenever
   the goal is a divisibility (Domain.div-from).  Lemma M and Euclid are
   stated for any gcd datum.
 * Content.seg: a content of e below n is a relation (a gcd of e_0..e_(n-1));
   every e merely has one (cont-exists); a content below n+1 is a gcd of
   e_n and any content below n (cont-gcd); cont-M and prim-M as before.
 * Gauss.seg: statement (C) is for every content of p and of q; each step
   takes gcd(d,p_0), gcd(d,q_0) and the contents it uses.
 * PolyGcd.seg: deciding x = 0 is a proposition, so it takes a content of x;
   integrality likewise; A[X] is then a discrete domain, so h | G takes a
   content of h; the gcd of f, g merely exists, taking c(f), c(g), c(D)
   and a gcd of c(f), c(g).
 Elimination, Degree, PolyBase and the library files are unchanged.

Check (from unit/):   ./segc sag/gcddomain-mere all
  2026-11-04: 24 modules, 0 failed, 0.13 s.

No new axioms; rests on the Theory parameters univ (univalence) and
images/surjections (replacement), used for A[X] as a quotient, for
function extensionality, and for the propositional truncation.
