Classical local-to-global etale covers from choice (sag/etale-choice-global)
============================================================================

This tree is sag/etale-classical-global and sag/choice-prime together:
every .seg file is a relative link to one of them (or to the libraries
they link), unchanged, except All.seg and ChoiceGlobal.seg.

Check (from unit/):   ./segc sag/etale-choice-global all
Fresh:                seg sag/etale-choice-global/All.seg
Result (31 October 2026): 4610 declarations, 0 failed, 1.46 s.

Theory: univalence and the two parts of replacement (univ, images,
surjections), as in every sag/ directory. Segment Ch has one parameter:

  ac : [l] (X : U l) (Y : X -> U l) -> isSet X -> ((x : X) -> isSet (Y x)) ->
       ((x : X) -> || Y x ||) -> || (x : X) -> Y x ||

Inside Ch:
  lem              derived (choice-prime/Diaconescu)
  prime-existence  derived (choice-prime/Krull, by Bourbaki-Witt)
  Global = Classical.Cl[lem,prime-existence]
                   the classical segment of etale-classical-global, its two
                   premises supplied; no other change.

ChoiceGlobal restates its endpoints with only ac as premise:
  Cover[A,setA,G].theorem          primewise good elements => merely a
                                   finite cover sum_i s_i a_i = 1
  Etale[A,setA,E,setE,iota].cover        (ClassicalEtaleCover.Given)
  Etale[A,setA,E,setE,iota].flat-cover   (ClassicalEtaleCover.GivenFlat)
  Etale[A,setA,E,setE,iota].monic-cover  (ClassicalEtaleCover.GivenMonic)
Each is settled by names; --opened reports nothing opened.

No new axioms: the Theory parameters univ, images, surjections and the
choice parameter ac. The scope is that of etale-classical-global (its
README, section 5): the local theorem is still a premise of the etale
endpoints, over the original base.
