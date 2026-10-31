Higher categories from the Sattler-Wärn axioms (sag/hcat)
=========================================================

Check:   ./segc sag/hcat all        (from unit/)
Design:  DESIGN.md; working rules: HANDOFF.md.  A port of ~/AGDA (Lemma 26),
continued with M6 (Segal for all n, composition and its laws) and M7
(fully faithful functors, Wärn results 33-39).

Theory: univalence and the two parts of replacement (univ, images,
surjections), fe derived from univalence.  The axioms of Cat are the
parameters of three nested segments of All.seg:
  Wild       Cat, Map, comp, idMap, comp-assoc, comp-id-l, comp-id-r
  Structure  cat-univalence, One, terminal, I, I-ob, pb, pb-pr1, pb-pr2,
             pb-comm, pb-is-equiv, Fun, ev, exp-is-equiv, I-mor-order,
             I-char-inverse, I-char-rinv, I-char-linv, segal-is-equiv,
             rezk, I-detects-equiv
  Coh2       pentagonator, triangle2
No new axioms.  Linked unchanged: Base, Prelude, Paths, Axioms, FunExtUA
(core), Replacement, EquivalenceLemmas, EquivProp, Equivalences,
AffineHLevels.

Theory level (paths in any type)
  PathAlgebra  groupoid laws with hidden endpoints (tassoc, unit-l, inv-l/r,
               canc-l/r, cancel-l/r, ap-trans, ap-sym, ap-comp, sym-trans)
  Cayley       solveR: reassociation by the Cayley action (shape syntax)
  GroupoidWords solveG: free-groupoid words (inverses as well)
  PathMoves    continuation-form moves for telescoping pasted 2-cells
  Finite       Sum, Two, Ord n, leq2, leqOrd
  EquivAp      ap-equiv (ap of an equivalence), pair paths

Wild (level 1)
  WildCat      ccl, ccr, composeA, post-comp, isIso (a proposition), Equiv-from
  Naturality   naturality of the reassociator and unitors, cancel-ccr/ccl-Id, xch
  Retracts     has-inverse-isIso, Lemma 25 (retract-iso)

Structure (level 1)
  HigherCat    Ob, terminal-is-prop (Remark 5), isIso-inverse
  Constructions I0, I1, bang, Mor, dom, cod, Hom, id-hom, Hom-map
  PullbackCone, Pullbacks  Cone, pb-comparison; times, pi1, pi2, pair,
               pair-beta1/2, pair-eta, pair-nat, cone-eq
  ExpComparison, Exponentials  exp-equiv, ob-map-equiv (Remark 16)
  ExpEval      exp-eval;  UnitIso  eval-pt-isIso
  OrdMonotone, MonotoneMaps, IntervalChar, Interval, Construction20
               monotone-ord, I-char, Delta, pointwise-to-mor,
               mor-to-pointwise, construction-20
  HLevels, SigmaEquiv
  ProductMap   product-map, ipe, prod-path-eq, pmc (locked)
  Squares      Square, sq-cone, sq-comparison, is-pushout-square,
               square-morphism, square-retract, times-I
  SquareAlg    retract-of-equiv, cone-eq, id-sqm, comp-sqm,
               MorphismEq.square-morphism-eq, sq-cone-pre

Coh2 (level 2)
  CatCoherence triangle1, triangle3 (from the pentagon), unit-loop
  MacLane      Mac Lane coherence: sound, coh, composeA-coh
  ProductPentagonFrames, ProductPentagon, ProductPentagonR, ProductPentagonR2
               prod-pent-C : product-map-eq1 1 (composeA k g h) = prodpent-rhs-C k g h
  ConeUnit     sq-cone-pre-id
  ConeAlg      cone-post, cone-post-comp, cone-pre-post, sq-comparison-natural
  ConeComp     leg-beta, leg-alpha, sq-cone-pre-comp
  PushoutRetract  is-pushout-square-retract (a retract of a pushout is one)
  TimesICone, TimesIPost, TimesI  times-I-preserves (-x I preserves pushouts)
  SegalGeom    base-Sq1 : is-pushout-square (Sq 1)
  Lemma26      S-step, S-pushout, lemma26-square : (n : Nat) -> is-pushout-square (Sq (suc n))

Structure, M3 and M5 geometry (level 1)
  OrdCompare, FaceOrd, OrdComb, LastEdge, FaceMap, FaceOrdCompat  faces and orders
  IntervalPosetal  I-hom-contr (proved; an Agda postulate)
  SegalComparison, Segal  the Segal comparison (axiom segal-is-equiv), comp-hom
  PosetalCore, FunIPosetal  is-posetal, posetal-hom-is-set, I-posetal, Delta-posetal
  FaceTop, PushoutBase, PushoutDef, PushoutProof  top, face-top, the case n = 0
  GluingSquare Sq n;  SegalCoface  segal-coface-01/12 (proved; Agda postulates)
  SimplexRetract, SimplexRetractValues, SquareGeom
               retract-SSk : square-retract (Sq (n+2)) (times-I (Sq (n+1)))
  ProdHomSet   prod-hom-is-set

Structure, M6 and M7 (level 1)
  FibreLemmas  fib, equiv-fibre-contr, fibre-contr-equiv, id-equiv-of-contr
               (fundamental theorem of identity types), equiv-ind,
               is-embedding, is-surjective, embedding-surjective-equiv,
               prop-equiv, cancel-equiv, prod-equiv, fibrewise-from-total
  Chains       HChain C n x (chains ending at x), TC, Chain-map,
               univ-chain n (the spine of Delta n), spine, spine-total
  HomPaths     Hom-eq, Hom-ends, subst-HChain-suc, chain-suc-eq
  Composition  Pair, Tri, bd (boundary of a 2-simplex), segal2-equiv,
               composite (locked) / hcomp, composite-witness,
               composite-filler, composite-agrees (= Segal.comp-mor)
  SpineTwo     spine-two: the spine at n = 2 is bd-pair
  Invertible   is-inv (postcomposition is an equivalence), is-inv-prop,
               ObIso, is-ff;  then the parameters rezk, I-detects-equiv

Coh2, M6 and M7 (level 2)
  SpineSquare  Sq-I (I for Delta 1), pushout-is-equiv : all n
  HomFunctor   Hom-map-of-comp (pentagon), Hom-map-id (Agda endpt), Hom-map-gen
  ChainFunctor Chain-map-of-comp
  SegalAll     segal-all : (n : Nat) (C : Cat) -> isEquiv (spine-total C n);
               segal-equiv, filler-contr
  CompLaws     Tri-map-of-comp, bd-nat, Hom-map-comp, Hom-map-hcomp,
               hcomp-unit-r, hcomp-unit-l
  Associativity  Quad, segal3, hcomp-assoc
  FullyFaithful  has-inv <-> is-inv, id-is-inv, functor-pres-inv,
               ff-reflects-inv (Lemma 35), idtoiso, rezk-idtoiso,
               isoact-equiv, rezk-square, ff-emb (Lemma 37),
               ff-surj-iso (Remark 39), iso-ff, iso-surj (its converse)

Axioms: the Theory parameters univ, images, surjections and the parameters of
Wild, Structure (cat-univalence, One, terminal, I, I-ob, pb.., pb-is-equiv,
Fun, ev, exp-is-equiv, I-mor-order, I-char-inverse/rinv/linv, segal-is-equiv,
rezk, I-detects-equiv) and Coh2 (pentagonator, triangle2).  No new axioms
beyond these; rezk and I-detects-equiv are Wärn's Axioms 36 and 38.
