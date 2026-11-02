Higher categories from the Sattler-Wärn axioms (sag/hcat)
=========================================================

Check:   ./segc sag/hcat all        (from unit/)
Design:  DESIGN.md; working rules: HANDOFF.md.  A port of ~/AGDA (Lemma 26),
continued with M6 (Segal for all n, composition and its laws) and M7
(fully faithful functors, Wärn results 33-39).

Theory: univalence and the two parts of replacement (univ, images,
surjections), fe and propUA derived from univalence.  The axioms of Cat are the
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
  Conj         conj a q = a^-1 . q . a and its laws; pent-solve, nat-alg
               (the path algebra of Loops.L-nat)
  Pi0          pi0 Y (components, by Quotient), pi0-map, pi0-equiv; LoopGrp
               (pi_1 as a group, QGrp); TransportGrp; is-abelian, loop-ab
  Pi0Maps      pointed maps induce loop-group homomorphisms; transport of
               homomorphisms along commuting squares of equivalences
  Pi1Product   zero of a product loop class is detected by its two projections
               and every pair of classes merely has a product lift
  AbelianDifference  product groups, difference homomorphisms and cancellation
  PullbackPaths, PullbackBoundary, PointedPullback
               paths of cones and the loop-difference kernel calculation
  PullbackExact  exactness at pi_1(P) for a pointed homotopy pullback
  PullbackNaturality  boundary naturality under maps of cospans with
               specified homotopies, including their pointing paths
  linked: Quotient, TruncationCombinators (sag/pn), Group, QGrp (sag/em), Torsor
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

Structure, type theory for homology groups (no Cat)
  FibreAlg     sigma-path-equiv, sigma-contr, fib-pr1, FibComp, RetractFib
               (r s ~ id gives fib s (s y0) ~ Omega (fib r ..)), OmegaFib
               (Omega fib F ~ fib (loop F)), ContrLoop, path-sym-equiv, ap-Equiv
               omega-fst retains the loop-fibre projection
  FibreSequence  exactness and homomorphisms for pi_1(fib f) -> pi_1(Y) -> pi_1(W)
  FibreInclusion  fibre of inclusion of a family fibre ~ loops in its base,
               retaining the projected path
  FibreTower   tower: recursive pointed fibre inclusions; exactness at all
               stages; Rotate: the second fibre is Omega W, over the boundary
  FibreTowerMaps, FibreTowerNaturality
               one pointed square induces commuting group squares throughout
               the tower, by recursion, without further coherence parameters
  PointedEquivalence  a pointed equivalence induces an equivalence of groups
  CommutingLoops  homotopies into a type with commuting loops induce equal
               loop maps with arbitrary pointing paths; factors and squares
  LoopDifference  looping difference gives group difference on pi_2
  LoopProduct  the actual two projections on pi_2 admit joint lifts
  PullbackFibre  the projection from a pullback to the product of its legs
               feeds the tower; one connecting map is additive and exact
  PullbackSource, PullbackDifference  the SAME boundary is exact at pi_2(P),
               with the usual difference of the induced maps on pi_2
  EckmannHilton  eckmann-hilton, comm-transfer, loop-comm

Structure, M6 and M7 (level 1)
  FibreLemmas  fib, equiv-fibre-contr, fibre-contr-equiv, id-equiv-of-contr
               (fundamental theorem of identity types), equiv-ind,
               is-embedding, is-surjective, embedding-surjective-equiv,
               prop-equiv, cancel-equiv, prod-equiv, fibrewise-from-total
  UniversalWitness paths, sections, globes-contr (all finite path dimensions),
               Witness.coherence, path-lifts: coherent uniqueness in fibres
               of equivalences, retaining the universal-property witness
  WitnessTransport Square.act, Identity.identity, Compose.composition;
               Square.coherence: transport and coherent comparison of
               universal witnesses along specified commuting squares
  Chains       HChain C n x (chains ending at x), TC, Chain-map,
               univ-chain n (the spine of Delta n), spine, spine-total
  HomPaths     Hom-eq, Hom-ends, subst-HChain-suc, chain-suc-eq
  HomEqHigher  Compare.ends, Compare.Move.move: compare Hom-eq paths
               including their endpoint 2-cells
  HomEqCoerce  Coerce.naturality: endpoint transport acts on Hom-eq
               by appending the explicit endpoint 2-cells
  HomEqMap     MapEq.naturality: Hom-map acts on Hom-eq by explicit
               associator-naturality and endpoint pastings
  HomFunctorPaths Change and Coerce: paths between functors and moving
               endpoints, with checked explicit normal forms
  HomCells     Cell retains the morphism path and endpoint cells;
               join, endpoint coercion and Hom-map agree with reading
  EquivIndBeta rule: computation of homotopy extension along an equivalence
  Composition  Pair, Tri, bd (boundary of a 2-simplex), segal2-equiv,
               composite (locked) / hcomp, composite-witness,
               composite-filler, composite-agrees (= Segal.comp-mor)
  SpineTwo     spine-two: the spine at n = 2 is bd-pair
  Invertible   is-inv (postcomposition is an equivalence), is-inv-prop,
               ObIso, is-ff;  then the parameters rezk, I-detects-equiv

Coh2, M6 and M7 (level 2)
  SpineSquare  Sq-I (I for Delta 1), pushout-is-equiv : all n
  HomFunctor   Hom-map-of-comp (pentagon), Hom-map-id (Agda endpt), Hom-map-gen
  HomCompEndpoints Normal.form-explicit: the existing Hom-map-of-comp
               with arbitrary endpoints, as explicit pentagon/naturality
               pastings; a bridge for the still-open triple coherence
  HomTriple    Triple.short, Triple.long: actual triple-composition paths;
               Triple.Coherence states their equality (proof still open)
  HomTripleShort  short-long-form: the actual short path as Hom-eq along
               the long morphism path, using the ambient pentagon
  HomTripleLongCells  form1-form5: the five actual long-path steps as cells
  HomTripleNormalize  long-form; from-endpoints reduces HMOC3 to two
               explicit endpoint equations, still to be proved from k5
  ChainFunctor Chain-map-of-comp
  SegalAll     segal-all : (n : Nat) (C : Cat) -> isEquiv (spine-total C n);
               segal-equiv, filler-contr
  CompLaws     Tri-map-of-comp, bd-nat, Hom-map-comp, Hom-map-hcomp,
               hcomp-unit-r, hcomp-unit-l
  Associativity  Quad, segal3, hcomp-assoc
  PentagonReduction assoc-on-spine, segal4, extend: computation of the
               chosen associator and reduction of its pentagon to spines
  AssocNat     associator naturality in paths between arrows
  CompWitness  Post.Assoc.coherence: postcomposition of a specified composite,
               conditional on its pentagon; independent of homology
  FullyFaithful  has-inv <-> is-inv, id-is-inv, functor-pres-inv,
               ff-reflects-inv (Lemma 35), idtoiso, rezk-idtoiso,
               isoact-equiv, rezk-square, ff-emb (Lemma 37),
               ff-surj-iso (Remark 39), iso-ff, iso-surj (its converse)

Homology (segment inside Coh2; DESIGN-HOMOLOGY.md), parameters
  level k < l, D : Cat, tensor (X : U k) (A : Ob D), eta, tensor-up
  (Hom (X (x) A) T ~ (X -> Hom A T): X (x) A is the copower, the
  colimit of the constant X-diagram at A, i.e. homology of X with
  coefficients A)
  CopowerRestrict restrict
  Copower      lift (locked), lift-beta, ext
  TensorMap    tmap, tmap-beta, restrict-tmap, tmap-id, tmap-comp, tmap-htpy
  CopowerWitness Maps.choices, TensorMaps.choices; Identity.comparison and
               Composite.comparison retain the beta compatibility
  CopowerPost  Post.lift-comparison, Compose.comparison: postcomposition
               of complete witnesses; comparison with the specified
               categorical associator remains open
  TensorInvariance  tmap-has-inv / tmap-is-inv (homotopy invariance),
               dim-has-inv / dim-is-inv (1 (x) A ~ A), empty-initial
  TensorSum    is-coproduct; SumOf.tensor-sum (additivity)
  Fubini       FubiniOf.fubini : (X * Y) (x) A ~ X (x) (Y (x) A)
  ExcCoreAlg, TypePushout, DPushout   pushouts of types (HtpyInd,
               TSquare.is-pushout), pushouts in D (DSquare, omega)
  WithPentagon (sub-segment, parameter hpent: the pentagon of D)
    ExcisionAssoc  rt-assoc (CompWitness instance, uses hpent)
    Excision     ExcisionOf.excision : TSq.is-pushout -> DSq.is-pushout
    Stable (sub-segment; parameters zobj, zero-init, zero-term, susp, merid,
            susp-po, stable (Hom (S, -) sends pushouts to pullbacks), unitD)
      Zero         zi, zt, zmap (the zero map), zero-post
      Cone         DCone: Cone, cone-map, is-pullback (representably)
      Loops        LoopOf.L : Hom (Sigma S, T) ~ Omega (Hom (S, T), 0), L-equiv,
                   L-nat (natural in T; uses hpent), L-zero
      ZeroCoherence  zero-post-path, Compose.coherence (uses hpent)
      ConeZero     cone-zero: the cone of zero is the pointed cone
      StableLoop   StabLoop.sigma : Hom (B, E) ~ Omega (Hom (B, Sigma E), 0)
      HGroups      Sph n, homology n X A = Pi0 Hom (Sph n, X (x) A); hgrp (groups
                   in degree n+1), hgrp-ab (abelian, degree >= 2), hgrp0,
                   hgrp-ab-stable (with stability: all degrees, abelian)
      HGroupMaps   hmap, hmap-id, hmap-comp (all degrees); Post.mul,
                   hmap-mul/one/inverse (positive degrees, existing hpent)
                   Degree-zero and connecting homomorphisms remain open.
      MayerVietoris  MV: mv-square, exact-mid, delta, delta-zero, exact-c, for a
                   pushout square of D; MVTypes: the excision instance
      MayerVietorisExact  delta-point-path; difference-zero, exact-p:
                   ker(delta) = im(u_* - v_*) at H_(n+1)(X), all n >= 0,
                   for the original boundary and existing group structures
      MayerVietorisLoop  a separate looped boundary is a homomorphism
                   H_(n+2)(X) -> H_(n+1)(C), all n >= 0. Agreement with the
                   original boundary remains open (ComponentCompatibility).
                   It has not replaced the boundary in the exactness proofs.
      HomologyFibre, HomologyFibreLegs, HomologyFibreExact
                   structural boundary H_(n+2)(X) -> H_(n+1)(C): a homomorphism
                   whose image is ker(i_*,j_*), using the EXISTING groups and
                   outgoing maps. Homomorphism and exactness now use ONE map.
      HomologyDouble  double-loop group equivalence and naturality via L-nat;
                   no coherence of the chosen basepoint paths is needed
      HomologyFibreSource  ker of the SAME boundary = image of usual u_*-v_*
      HomologySequence  all three repeating positive-degree exactness positions,
                   usual maps and one connecting homomorphism, all between the
                   EXISTING abelian groups; consecutive pieces agree.
                   Degree zero and categorical naturality remain open.
      Suspension   Red S X A (reduced homology, fibre of Hom (S, t!)), reduced,
                   is-suspension, SuspOf.susp-red : Red (Sigma S) SX A ~ Red S X A,
                   susp-iso : reduced (n+1) SX A ~ reduced n X A
      WithSpheres (sub-segment; parameters tsusp, tnorth, tsouth, tmerid,
            tsusp-po: suspensions of types; desusp, desusp-eq)
        Spheres    sphere n (S^0 = Sigma Empty); red-empty, dim-equiv, red-shift,
                   sphere-above (no desusp), red-sphere, sphere-homology
                   (H~_(n+j)(S^n; A) ~ Pi0 Hom (Sph j, A)), sphere-below

Coh3 (segment inside Coh2), parameter k5 : route1 = route2 (Stasheff K5)
  K5Hom        Triple.coherence: the k5 endpoint pastings lift to equal
               Hom paths; identification with Hom-map-of-comp is open
  CatK5        K5[A..F,f,g,h,e,d]: L, R, the faces P1-P6, N1-N3, route1, route2
  HcompPentagon  Pentagon C f1 f2 f3 f4 (statement of the internal pentagon)
  HomEqCalc    end-trans, Hom-ends-trans, HE-trans (composition of Hom-eq)

Axioms: the Theory parameters univ, images, surjections and the parameters of
Wild, Structure (cat-univalence, One, terminal, I, I-ob, pb.., pb-is-equiv,
Fun, ev, exp-is-equiv, I-mor-order, I-char-inverse/rinv/linv, segal-is-equiv,
rezk, I-detects-equiv) and Coh2 (pentagonator, triangle2), and for the homology files the parameters
of Homology (D, tensor, eta, tensor-up), hpent, the parameters of Stable
(zobj, zero-init, zero-term, susp, merid, susp-po, stable, unitD) and of
WithSpheres (tsusp, tnorth, tsouth, tmerid, tsusp-po, desusp, desusp-eq).  No new axioms
beyond these; rezk and I-detects-equiv are Wärn's Axioms 36 and 38.
