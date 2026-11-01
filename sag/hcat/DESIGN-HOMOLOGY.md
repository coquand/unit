# sag/hcat: homology as a colimit (segment Homology)

## Idea

Cohomology of a type X is a limit of the constant X-diagram: H^n(X;A) = ‖X → K(A,n)‖₀,
computed by Π because forgetful functors preserve limits. Homology is the dual colimit:
the colimit over X of the constant diagram at A, in a category D of "abelian" objects
(spectra, or D(Z)). This colimit is not Σ, since forgetful functors do not preserve
colimits. So homology needs X-indexed colimits in a category other than the universe.

For a constant diagram this colimit is the **copower** X ⊗ A:

  Hom(X ⊗ A, T) ≃ (X → Hom(A, T)),   g ↦ (x ↦ η_x g).

A diagram X → D from a groupoid into a Rezk-complete D is a function X → Ob D. The
constant ones are all that ordinary homology H(X;A) needs. Intended model: D the
∞-category of spectra, X ⊗ A = Σ^∞X₊ ∧ A. Then π_n(X ⊗ HZ) = H_n(X;Z).

## Parameters (segment `Homology`, inside `Coh2` of All.seg)

```
level k ; constraint k < l ;
D : Cat ;
tensor (X : U k) (A : Ob D) : Ob D ;
eta (X : U k) (A : Ob D) (x : X) : Hom D A (tensor X A) ;
tensor-up (X : U k) (A T : Ob D) : isEquiv (restrict X A T) ;
```

The size constraint k < l is needed. Objects of a category in Cat form a type in U l.
If D had copowers by every type of U l, Freyd's argument would make D a preorder, taking
X = Σ_C Hom(C,T) and comparing cardinalities.

## Milestones

### Universal witnesses and coherence (2026-11-01)

The first general coherence result is now checked in ordinary dependent type
theory. `UniversalWitness.globes A n` encodes a finite globular boundary and
its cell type using Nat, Sigma and identity types. `globes-contr` proves, for
every n and every such boundary, that its cells are contractible when A is.
Applied to the fibre of an equivalence, `Witness.coherence` gives coherent
uniqueness of universal witnesses at every finite path dimension.
`sections` gives the corresponding contractibility for dependent families
of choices; `path-lifts` gives contractible lifts of a specified path with
fixed endpoints, including the beta 2-cell.

`CopowerWitness` applies this to the fibres of restrict. The existing lift
and its beta law form a witness. The identity and composition comparisons
are paths of witnesses, retaining compatibility with the prescribed
restriction. All higher comparisons within the same fibre are covered by
`Witness.coherence`. These comparisons are additional constructions; their
projections have not been identified with the existing tmap-id/tmap-comp
proof terms.

The postcomposition issue is separate. `CompWitness.Post` starts with any
specified composite beta : ey tf = ez and derives the compatibility of its
postcomposition paths from the pentagon at (ey, tf, phi, g). It uses no
copower data. `ExcisionAssoc.rt-assoc` is now an application of this generic
lemma, and the existing excision proof still checks.

This proves coherent uniqueness for boundaries already expressed in a
universal-witness fibre. It does not prove that every categorical pasting
defines such a boundary, nor remove hpent or derive it from k5. The remaining
problem is coherent transport of witnesses by categorical operations.
No new axioms or changes to type theory were introduced: the existing
Theory parameters (univ, images, surjections), Cat parameters, copower
parameters and the existing hpent suffice. The witness lemma uses univalence
through equivalence fibres and function extensionality; it does not yet use
Rezk univalence to identify different representing objects.

### Transport of witnesses (2026-11-01)

This complements the concurrent H4-H5 development (zero objects, suspension,
loops, homology groups); it uses none of its additional stable parameters.
`WitnessTransport.Square` transports fibres along a specified commuting
square, retaining the beta path. Identity and pasting laws are proved by
ordinary path algebra. If the target vertical map is an equivalence, the
type of fibre maps is contractible; `Square.coherence` gives all finite
globular comparisons of these maps.

`CopowerPost.Post` applies this to postcomposition: the square between
restriction and postcomposition commutes by the pointwise inverse
associator. Its transported chosen lift agrees with the chosen lift of
the postcomposed generators in the witness fibre (`lift-comparison`).
`CopowerPost.Compose` compares successive and direct postcomposition after
moving the former along the pointwise associator on generators. This
comparison retains beta compatibility and uses only Coh2 and the existing
copower parameters. Its projection has not been identified with D's
specified associator; no pentagon has been discharged by this argument.

- **H1 (done).** `CopowerRestrict`, `Copower` (lift, lift-beta, ext; lift locked) and
  `TensorMap`: functoriality of X ↦ X ⊗ A, via tmap, tmap-beta, restrict-tmap, tmap-id,
  tmap-comp and tmap-htpy.
- **H2 (done).** The Eilenberg–Steenrod axioms that need no 2-cells:
  - `TensorInvariance`: homotopy invariance (an equivalence X ≃ Y gives an invertible
    tmap), dimension (η_tt : A → 1 ⊗ A is invertible), and 0 ⊗ A initial;
  - `TensorSum`: additivity, (X + Y) ⊗ A a coproduct of X ⊗ A and Y ⊗ A;
  - `Fubini`: (X × Y) ⊗ A ≅ X ⊗ (Y ⊗ A).

  All of these are at level 2 of Cat. They use associativity and the unit laws of D,
  which are internal level 1.
- **H3 (done, modulo the pentagon of D): excision.** For a pushout square of types (maps out
  of X are cocones, targets in U l), the square tmap i, tmap j, tmap u, tmap v with its 2-cell
  `cell` is a pushout in D: precomposition with the square, whose path part is built from
  associators of D, is an equivalence `Hom(X ⊗ A, T) ≃ Cocone_D(T)`. Files: `ExcCoreAlg`,
  `TypePushout`, `DPushout`, `AssocNat` (Coh2); `ExcisionAssoc`, `Excision` (segment
  `Homology.WithPentagon`).

  The only extra assumption is `hpent`, the pentagon of D's composition (`HcompPentagon`).
  It is used once, in `ExcisionAssoc.rt-assoc`, at (η_y, tmap f, φ, g).
- **Coh3 (stated).** `CatK5` defines the two pastings route1 and route2 of the faces of
  Stasheff's K5 for five maps. Each route uses three pentagonators and two of the three
  naturality squares, from L = a((fg)h,e,d)·a(fg,h,ed)·a(f,g,h(ed)) to the six-step path R.
  The segment `Coh3` has the parameter `k5 : route1 = route2`.
- **H3a (open): the internal pentagon from Coh3**, to discharge `hpent`. Plan:
  Checked supporting results (2026-11-01):
  - `HomEqHigher.Compare.ends` and `.Move.move`: compare Hom-eq paths
    while retaining endpoint 2-cells, including a change of the underlying
    morphism path. These use identity elimination in Structure.
  - `K5Hom.Triple.coherence` (Coh3): apply the actual k5 parameter at I0
    and I1 and lift its two pastings to equal paths in Hom. The source
    endpoint paths are K5.L; the target endpoint paths are the last three
    reassociations. Both lifted paths use the long, three-step morphism
    path. Identifying these normalized lifted paths with the composites
    of the existing Hom-map-of-comp is still open; this is not HMOC3 yet.
  - `HomCompEndpoints.Normal.form-explicit` (Coh2): identifies the existing
    Hom-map-of-comp for arbitrary endpoint paths with Hom-eq whose endpoint
    cells are explicit pastings of the base pentagon, naturality in the
    third argument, ap-trans and path associators. This handles the
    non-reflexive endpoints introduced by a preceding functor. The proof
    uses J and a checked reflexive computation; HomFunctor is unchanged.
    The remaining HMOC3 comparison needs the action of Hom-coerce and
    Hom-map on these Hom-eq paths and normalization of their composite
    endpoint cells to the K5 routes.
  - `HomEqCoerce.Coerce.naturality` (Structure) proves the Hom-coerce
    action on Hom-eq, with explicit appended endpoint 2-cells. Its
    reflexive computation includes ap-id for the Hom path and both
    endpoint witnesses. The HE-trans composition rule is already available.
  - `HomEqMap.MapEq.naturality` (Structure) now proves the Hom-map action
    on Hom-eq, with explicit endpoint cells using associator naturality
    in its middle argument. Its reflexive case and endpoint comparisons
    are proved by J; no truncation of Hom or its identity types is used.
  - `HomFunctorPaths` gives the comparisons for a path between functors
    and for Hom-map commuting with endpoint transport; `.form` identifies
    each with its explicit Hom-eq/Hom-ends expression.
  - `HomTriple.Triple.short` and `.long` are the two actual paths built
    from the existing Hom-map-of-comp proofs. Their common endpoints
    and all vertex transports are checked. `.Coherence` is their equality
    TYPE, still without a proof. This is the concrete HMOC3 target for
    the canonical morphism input.
  - `HomTripleShort.short-long-form` identifies the actual short path
    with Hom-eq, moving its arrow along the ambient pentagon.
    `HomCells` bundles the existing Hom-eq calculation rules.
    `HomTripleLongCells.form1` through `.form5` identify each actual
    step of the long path; `HomTripleNormalize.long-form` joins them
    and removes the reflexive arrow steps. Both paths now use the SAME
    underlying morphism path, with explicit endpoint cells.
    `HomTripleNormalize.LeftCoherence` and `.RightCoherence` are the
    remaining endpoint equality types; `.from-endpoints` proves that
    they imply the original HMOC3 equation. Neither equality has been
    derived from k5. Identifying these cells with the K5 routes remains
    open, followed by steps 2-5 below; hpent is still assumed.
  - `EquivIndBeta.rule`: the chosen extension of a homotopy along an
    equivalence restricts to the original homotopy, proved by univalence.
    `PentagonReduction.assoc-on-spine` applies it to the actual
    hcomp-assoc proof term, identifying it with OnSpine.result.
  - `PentagonReduction.segal4` and `.extend`: reduce the pentagon for
    arbitrary four arrows to its value on a 4-simplex spine. The proof
    on these spines is an argument to extend, not a new axiom or a result
    already proved. In particular hpent remains an explicit assumption
    of the homology development.
  1. `HMOC3`: coherence of Hom-map-of-comp for three functors. By J on the endpoints of h,
     it reduces to h = (m, refl, refl). The morphism parts agree by the pentagon P(F,G,K,m).
     The endpoint 2-cells are compared by K5 at (F,G,K,m,I0), and at I1. The starting
     endpoint path is K5's L, side 1 follows route1, and side 2 follows route2 up to its
     last face. Started: `HomEqCalc` (end-trans, Hom-ends-trans, HE-trans).
  2. `TRI-PENT`: the same coherence for Tri-map-of-comp. The vertices use the pentagon at
     objects, the edges use HMOC3.
  3. Functors carry composition witnesses to composition witnesses:
     Hom-map-hcomp (F G) = HMOC · F(Hom-map-hcomp G) · Hom-map-hcomp F (Gp). Proved through
     fillers: composite-witness is an equivalence on fib(bd, t), and the fillers (FG)s and
     F(Gs) are compared by TRI-PENT.
  4. Associators are natural under functors:
     al(Fu,Fv,Fw) = Hom-map-hcomp-conjugate of Hom-map F (al(u,v,w)). By equiv-ind over
     3-simplices S of the source: on spines, both sides are OnSpine results, related by
     step 3.
  5. The pentagon at the spine of T : Δ4 → C (equiv-ind along Segal at n = 4). By step 4
     each associator is a conjugate of Hom-map T of a path in Δ4. The conjugations
     telescope, and two parallel paths in Hom Δ4 (a proposition) are equal.
- **H4 (done, modulo hpent).** Pointed and stable D, and the homology groups.
  Sub-segment `Homology.WithPentagon.Stable`, parameters:
  ```
  zobj : Ob D ; zero-init T : isContr (Hom zobj T) ; zero-term T : isContr (Hom T zobj) ;
  susp B : Ob D ; merid B : zmap B (susp B) = zmap B (susp B) ;
  susp-po B : DSquare[B, zobj, zobj, susp B, zt B, zt B, zi, zi, merid B].is-pushout ;
  stable (any DSquare) (po : is-pushout) : DCone[..].is-pullback ;
  unitD : Ob D ;
  ```
  **Choice of stability.** `stable` says that Hom(S, -) sends every pushout square of D
  to a pullback of types (`Cone.DCone.is-pullback`): the representable form of "pushout
  squares are pullbacks". It needs no pullbacks in D, and it is what the Mayer–Vietoris
  and suspension arguments use: Hom(S, -) of the excision square, and of the suspension
  square 0 ← E → 0. Only pushouts 0 ← B → 0 are assumed (suspensions). "Σ is an
  equivalence" splits into fully faithful, which follows from `stable`
  (Hom(B, E) ≃ Ω Hom(B, ΣE), `StableLoop`), and essentially surjective, which is needed
  only for H̃_k(Sⁿ) with k ≤ n and is the parameter `desusp` of `WithSpheres`.
  Results:
  - `Zero`: zi, zt, zmap, zero-post (0 f = 0).
  - `Loops.LoopOf.L`: Hom(ΣS, T) ≃ Ω(Hom(S, T), 0) (susp-po, then the contractible
    Hom(0, T)); `L-nat`: natural in T, by the pentagon at (zt S, zi, g, f) (the second use
    of hpent) and assoc-nat-l; `L-zero`: L 0 = refl. The path algebra is the generic
    `Conj.pent-solve`, `Conj.nat-alg`.
  - `HGroups`: Sph n = Σⁿ𝟙, homology n X A = Pi0 Hom(Sph n, X ⊗ A). `hgrp n X A`, a group
    on homology (n+1) X A, moved along Pi0 of L from π₁(Hom(Sph n, X ⊗ A), 0)
    (`Pi0.LoopGrp`, `Pi0.TransportGrp`); `hgrp-ab`: abelian in degrees ≥ 2
    (Eckmann–Hilton through L). With stability: `hgrp0` on homology 0 X A (moved along
    `StableLoop.sigma`), and every group abelian (`hgrp-ab-stable`, `stab-grp-ab`).
    Not proved: that the two structures on homology (n+1) agree.
  - `HGroupMaps` (2026-11-01): `Post.mul` proves that postcomposition
    preserves the chosen `LoopGroup` multiplication. `Pi0Maps.Pointed`
    proves that a pointed map induces a loop-group homomorphism, and
    `Pi0Maps.Transport` transfers this property along a commuting square
    of equivalences. The square here is exactly `Loops.L-nat`.
    Consequently `hmap-mul`, `hmap-one`, and `hmap-inverse` prove that
    maps of types induce homomorphisms in EVERY POSITIVE degree, for
    the existing `hgrp` structures. `hmap-id` and `hmap-comp` hold in
    all degrees as equalities of functions evaluated at each element.
    No compatibility of the L-nat witnesses with composition is used;
    no parameter beyond the existing hpent is needed. The degree-zero
    homomorphism for `hgrp0` and the original connecting homomorphism remain open.
  - `MayerVietorisLoop` (2026-11-01): a positive-degree connecting
    homomorphism obtained by looping the previous pointed boundary:
    `deltaLoop_S = L_(S,C)^-1 . Omega(delta_S) . L_(Sigma S,P)`.
    Its `mul`, `one`, and `inverse` use the existing LoopGroup structures
    and hpent only. This map is kept separate from the original
    `MayerVietoris.MV.delta` at Sigma S. Agreement is NOT proved.
    `ComponentCompatibility` records the sufficient comparison on pi0;
    `original-mul-components` transfers additivity if that comparison is
    proved. Neither compatibility type has been added as a parameter.
  - Type theory used (linked or new, no Cat): `Pi0` (sets of components via
    `Quotient`, loop groups via `QGrp`, from sag/em and sag/pn), `EckmannHilton`,
    `FibreAlg` (fibre lemmas, `RetractFib`, `OmegaFib`, `ContrLoop`), `Conj`.
- **H5 (done in the forms below).**
  - `MayerVietoris.MV`, for any pushout square of D and any S: `mv-square`
    (u_* i_* = v_* j_*), `exact-mid` (the kernel of (u_*, v_*) is merely the image of
    (i_*, j_*), as sets of components), the connecting map `delta` :
    Hom(ΣS, P) → Hom(S, C), `delta-zero` and `exact-c` (exactness at H(C)).
    `MVTypes` instantiates it with the excision square: H_{n+1}(X) → H_n(C) →
    H_n(B) × H_n(E) → H_n(X).
  - `MayerVietorisExact` (2026-11-01) proves the remaining position:
    `difference-zero` and `exact-p` identify the kernel of the original
    boundary H_(n+1)(X) -> H_n(C) with the image of the ordinary group
    difference u_* - v_* in H_(n+1)(X), for every n >= 0.
    `delta-point-path` also proves that the original boundary is pointed.
    `ZeroCoherence` proves compatibility of zero-post with composition
    using hpent, and `ConeZero` identifies the cone of zero with the
    pointed pullback cone. `PullbackPaths`, `PullbackBoundary`,
    `PointedPullback`, and `PullbackExact` prove the generic path and
    component arguments in Theory, with no Cat parameters.
    The three repeating exactness positions are now proved, with the
    middle position still expressed as equality u_* b = v_* e in degree
    zero. This is not yet a natural LES of abelian groups: additivity of
    the original boundary, degree zero, and categorical naturality remain
    open. The separate looped boundary above is not substituted into the
    exactness statements without a comparison proof.
  - `PullbackNaturality` proves boundary naturality for maps of pointed
    homotopy pullback diagrams with specified cospan homotopies. This
    uses only identity types. Instantiating it for maps of the categorical
    squares, with all the required comparisons, remains to be done.
  - **Structural reconstruction (2026-11-01).** `FibreSequence` proves
    exactness of pi_1(fib f) -> pi_1(Y) -> pi_1(W) for a pointed map
    f:Y->W. Both arrows are the same homomorphisms used in the exactness
    proof. `FibreAlg.OmegaFib.omega-fst` retains the projection of the
    loop-fibre equivalence; this is the decisive additional witness.
    `FibreTower.tower` repeatedly takes the pointed fibre inclusion.
    `At` supplies homomorphisms and exactness at EVERY stage from this
    finite recursive definition. `Rotate` identifies the second fibre
    with Omega of the original target, over the boundary map.
    `FibreTowerMaps.ArrowMap` is one pointed square, including its
    basepoint compatibility. `maps` recursively constructs all its fibre
    squares; the next basepoint compatibility is Sigma-path's projection
    beta, not a new parameter. `FibreTowerNaturality.At` proves that the
    induced squares of groups commute at every stage.
  - `PullbackFibre` applies the theorem to the projection of a homotopy
    pullback onto the product of its two legs. Its fibre is equivalent
    to the loop space of the apex, OVER the boundary into the pullback.
    The resulting connecting homomorphism is exact at pi_1(pullback).
    `PointedEquivalence` supplies equivalences of fundamental groups.
  - `HomologyFibre`, `HomologyFibreLegs`, `HomologyFibreExact` instantiate
    that construction using the EXISTING hpent, stability, and copowers.
    The structural boundary H_(n+2)(X) -> H_(n+1)(C) is a homomorphism
    between the existing abelian groups; its image is the simultaneous
    kernel of the existing i_* and j_* maps, for every n >= 0.
    This closes the previous separation of additivity and exactness at
    the target: they now concern ONE map. The old direct boundary need
    not be compared to it to obtain this result.
  - **Positive-degree sequence (2026-11-01).** `FibreInclusion` identifies
    the fibre of inclusion of a family fibre with loops in the base,
    retaining the projection. `PullbackSource` applies this to the
    boundary, identifying its fibre with Omega(B*E) over loop difference.
    `LoopDifference` and `PullbackDifference` identify the induced map
    on pi_2 with ordinary group difference, giving source exactness for
    the SAME structural boundary.
    `CommutingLoops` proves that, when loops at the target commute,
    homotopic maps induce equal loop maps for arbitrary pointing paths.
    Thus `HomologyDouble` proves naturality of the double-loop
    equivalence from L-nat WITHOUT a new basepoint 2-cell. This removes
    the previously suspected need for a higher coherence of L here.
    `HomologyFibreSource` transports source exactness to the EXISTING
    groups and usual postcomposition difference. `HomologySequence`
    packages all three repeating exactness positions, with the usual
    i_*, j_*, u_*-v_* and ONE connecting homomorphism. Every arrow is a
    homomorphism of the existing abelian groups. Consecutive pieces
    agree definitionally. The positive tail ends at H_1(X); no exactness
    assertion at that final term. The older boundary formula is unused.
    `HomologyFibreLegs` now uses one lemma for both projections, with no
    separate comparison of their pointing paths.
    Remaining: degree zero and categorical naturality. Do not claim
    the full conventional NATURAL LES yet. No new axioms or parameters;
    hpent remains assumed and H3a remains open.
  - **Reduced homology** is `Suspension.Red S X A = fib (c ↦ c t!) 0` on
    Hom(S, X ⊗ A), t! = tmap (X → 1): Hom(S, -) of the fibre of X ⊗ A → 1 ⊗ A, so no
    cofibres in D are needed (in stable D the fibre is Ω of the cofibre of the
    handoff). reduced n X A = Pi0 Red (Sph n) X A.
  - `Suspension.SuspOf.susp-red`: for any suspension SX of X (`is-suspension`: a TSquare
    pushout 1 ← X → 1), Red (ΣS) SX A ≃ Red S X A; `susp-iso`: reduced (n+1) SX A ≃
    reduced n X A. Proof: both sides are Ω(F, zF), F = Red S SX A. Left: excision +
    stability give Hom(S, X ⊗ A) ≃ (a, b : S → 1 ⊗ A) × (a tN = b tS), so Red S X A is
    fib (- tS) at 0, and tS r = id gives `RetractFib`. Right: L, L-nat, L-zero and
    `OmegaFib`.
  - `Spheres` (sub-segment `WithSpheres`, parameters `tsusp, tnorth, tsouth, tmerid,
    tsusp-po` — suspensions of types by their universal property, no HITs — and
    `desusp, desusp-eq : susp (desusp B) = B`): sphere 0 = Σ∅, sphere (n+1) = Σ sphere n.
    `red-empty`: Red S ∅ A ≃ Hom(ΣS, 1 ⊗ A); `dim-equiv` (dimension axiom);
    `sphere-above`: H̃_{n+j+1}(Sⁿ; A) ≃ Pi0 Hom(Sph (j+1), A) without desusp;
    `sphere-homology`: H̃_{n+j}(Sⁿ; A) ≃ Pi0 Hom(Sph j, A), so H̃_n(Sⁿ; A) ≃
    Pi0 Hom(𝟙, A) = H_0(1; A); `sphere-below`: H̃_k(S^{k+m}; A) ≃ Pi0 Hom(desusp^m 𝟙, A).
    All as bijections of sets.
- **H6.** A model: D = spectra, or the universe with X ⊗ A = X × A for a sanity check of
  the copower axiom (not stable).
