Excluded middle and prime ideals from choice (sag/choice-prime)
================================================================

Check (from unit/):   ./segc sag/choice-prime all
Fresh:                seg sag/choice-prime/All.seg
Result (31 October 2026): 1918 declarations, 0 failed, 0.46 s.
Every new declaration 0.00 s, at most 16 definitions opened (--opened).

Theory: univalence and the two parts of replacement (univ, images,
surjections), fe and propUA derived, as in every sag/ directory.
Segment Ch has one parameter, the axiom of choice for families of sets
over a set, at every level:

  ac : [l] (X : U l) (Y : X -> U l) -> isSet X -> ((x : X) -> isSet (Y x)) ->
       ((x : X) -> || Y x ||) -> || (x : X) -> Y x ||

(HoTT book 3.8.1; compatible with univalence). No other axiom.

Results, with exactly the types of the parameters of segment Cl of
sag/etale-classical-global/Classical.seg:

  Ch.lem : [l] (P : U l) -> isProp P -> P + not P
  Ch.prime-existence : [l] (A : CRing) -> isSet A.R ->
       PrimeExistence[l].Over[A].Principle

so Cl[lem, prime-existence] can be instantiated inside Ch. PrimeExistence.seg
is a link to that directory's file, unchanged.

Files (informal proof at the head of each):

  Diaconescu    choice gives excluded middle (HoTT book 10.1.14): the quotient
                of Bool by "a = b or P", a section of its quotient map.
  Resizing      with excluded middle every proposition is Top or Empty, so
                propositions of level l+ have copies of level l; dne.
  BourbakiWitt  for subsets of a type X and an inflationary f: the least tower
                containing b closed under f and unions of inhabited chains;
                Lemma 1 (Sides), Lemma 2 (extreme-all), the tower is a chain,
                its union top is in the tower and f top <= top.  Generic: no
                rings, only excluded middle.
  Krull         every proper ideal I (propositional membership) lies in a
                prime ideal: choice picks for every subset S a "successor"
                (strictly bigger good subset when one exists), Bourbaki-Witt
                gives a maximal proper ideal above I, and a maximal ideal is
                prime (1 = u + r x gives y = y u + r (x y)).

Reused by relative links, unchanged: core (Base, Prelude, Paths, Axioms,
FunExtUA), replacement (Replacement, Truncation, TruncationCombinators),
projective/Quotient, polynomial, presentations, affine, cffr/RegularIdeal and
the exterior chain it needs (same import list as etale-classical-global),
cca/BooleanRing (bool-set), etale-classical-global/PrimeExistence.
