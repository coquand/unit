Noetherian rings and the Hilbert basis theorem, without inductive families
=========================================================================

Check from unit/:

    ./segc sag/noetherian all

Pure algebra: no univalence, replacement, choice, decidable equality or
other module parameter. 13 modules, 0.05 s.

Sources: T. Coquand, H. Persson, Groebner bases in type theory (TYPES 98),
Section 3.1 (CPersson.pdf); Bishop's letter on noetherian rings
(bishop.jpeg); R. Kuroki, A quantitative Hilbert's basis theorem and the
constructive Krull dimension (ryoti.pdf).

The definition
--------------

Coquand-Persson define R noetherian as "Good bars []", an inductive
predicate on lists. Unit has no inductive families, so the derivation is a
datum, as in Bishop's letter (an ordinal and a rank): a tree branching
over the codes (Bar.Tree, a Brouwer ordinal with that branching type) with
the predicate Valid t s, defined by recursion on t. Bar.Over.Ind is the
elimination principle of the inductive definition.

Codes. Span.Pres[S] presents a subring of S by a type K of codes and a map
phi : K -> S preserving the ring operations (no laws on K). Elements of
quotients and localisations need not have chosen representatives; the
codes are the representatives the proof uses, and coefficients of linear
combinations are codes too. Good s: some phi(s_k) is a K-combination of the
earlier ones. Noeth: Good bars the empty list.

Results
-------

Field.Over.noeth              a discrete field is noetherian.
Transfer.Over.noeth           a ring map S -> S' carries a noetherian
                              presented subring to its image (same codes,
                              same tree). With a surjection: quotients, by
                              any ideal.
Hilbert.Over.hilbert          if P presents a noetherian subring of S,
                              then for every X in S, polynomial codes over
                              P (PolyPres, evaluation at X) present a
                              noetherian subring: P[X] in S. With S = R[X]
                              this is the Hilbert basis theorem; with
                              S = R[1/s], X = 1/s, it gives localisations.
Integers.Over.noeth           the image of Z in any ring is noetherian
                              (codes (a,b) for a - b; Euclid with
                              remainders, Kuroki's omega-Euclidean).
Generated.Over.noeth          iterating: P[x_1, .., x_n] in S.
Generated.Over.ascending      the content: along every sequence of codes,
                              some element is a combination of the earlier
                              ones.

Sequence.Over.Kill            if u = f^n w_n and f^(n+1) w_n = 0 for all n
                              and some w_k is a combination of the earlier
                              w_j, then u = 0; Walk finds such a k along
                              merely coded w_n, in any monad (truncation).
                              Used by sag/jacobian in place of a uniform
                              stabilization of annihilators.

The proof of the basis theorem is Coquand-Persson's: open induction on the
length of the newest polynomial code (Hilbert.open-ind), and their Lemma 15
by recursion on the tree of the leading coefficients (Hilbert.main). Their
Lemmas 7 and 13 are Span.bars-ins and Span.bars-rep: the same tree remains
valid after inserting elements, or after changing an element by a
combination of earlier ones. The informal proof is in the header of
Hilbert.seg.

Not done
--------

- Giving presentations to the existing PolynomialRing, Quotient and
  PowerLocalization rings as rings in their own right (sag/jacobian does
  the case it needs inside CodedCoefficients).
- Kuroki's quantitative version (alpha-Noetherian, omega (x) alpha for
  polynomials, Krull dimension bounds).
