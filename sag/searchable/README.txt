Searchable sets and the compactness of N-infinity, after M. H. Escardo,
"Infinite sets that satisfy the principle of omniscience in any variety of
constructive mathematics" (J. Symbolic Logic 78, 2013), as in his Agda
development TypeTopology.

Theory parameter: function extensionality only (no univalence, no
replacement).  No new axioms.

Files
  Decisions   (link to ../freegroup) Booleans as decisions: so, cases, Plus
  NInfty      N-infinity: decreasing binary sequences, under n, infinity,
              equality pointwise; First.first-zero: a sequence with a 0 is
              under m for some m
  Search      Searchable X (a selection function e with p (e p) = 1 =>
              p x = 1 for all x), Omniscient X; omniscient (searchable =>
              omniscient), bool-searchable, SigmaS.searchable (Sigma of
              searchable types), product-searchable, decide-eq (equality of
              Boolean functions on a searchable type is decidable)
  Compact     Eps[p].e = (n |-> p (under 0) and .. and p (under n));
              ni-searchable : Searchable NI, ni-omniscient,
              ni-decide-eq (f g : NI -> 2: they differ somewhere or agree
              everywhere), ni2-searchable
  Cantor      Bits n (finite words) searchable; UC n p (p has modulus of
              uniform continuity n); uc-search, uc-omniscient: the Cantor
              space is searchable for uniformly continuous predicates
  WLPO        WLPO <-> some f : N-infinity -> 2 is discontinuous at
              infinity (f (under n) = 0 for all n, f infinity = 1):
              wlpo-discontinuous, discontinuous-wlpo

Check (from unit/):   ./segc sag/searchable all
  2026-11-05: 11 modules, 0 failed, 0.02 s (249 declarations).
