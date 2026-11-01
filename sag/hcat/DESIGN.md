# sag/hcat: higher categories from the Sattler–Wärn axioms

A port to Unit of the Agda development `~/AGDA` (github.com/coquand/basic-higher-category),
then its continuation. The first aim is Lemma 26: for every n, the square gluing Δ¹ to Δⁿ
along a vertex is a pushout with corner Δⁿ⁺¹. The next aim is the Segal condition for all n
and composition of morphisms with its laws.

## Sources

- D. Wärn, *Higher-categorical headcanon* (`~/AGDA/axioms.pdf`, 17 pages). This is the
  numbering used by the Agda files: Axiom 1 (Cat), 3 (univalence of Cat), 4 (terminal
  category), 36 (Rezk), 38 (I detects equivalences), results 33–39 (fully faithful functors).
- C. Sattler and D. Wärn, *Axioms for higher category theory*, HoTTUF 2026 abstract,
  Axioms 1–14 (cited below as SW1–SW14).
- Cisinski, Cnossen, Nguyen and Walde, *Synthetic Category Theory* (draft), which both
  follow.
- The Agda proof and its handoffs: `~/AGDA/README.md`, `HANDOFF-lemma26-overview.md`,
  `HANDOFF-lemma26-posetal.md`, `HANDOFF-lemma26-pushout.md`,
  `HANDOFF-fullyfaithful-coherence.md`. The Rocq proof it was ported from
  (`~/Desktop/LUCIE/Main.v`) is not used.

## Principles

1. **Plain dependent type theory.** There is no judgemental shortcut for Cat: SW1 (5)–(6),
   strict associativity and unit laws of functor composition, is not assumed. The
   coherences of Cat are ordinary paths given as parameters.
2. **Every axiom is a segment parameter.** Nothing is postulated. The foundations are
   those of `sag/`: the parameters `univ`, `images` and `surjections` of `Theory`, with
   function extensionality derived.
3. **Coherence levels are layers.** Each level of coherence of Cat is the parameter of
   its own segment, nested in order. A file is imported in the outermost segment whose
   parameters it needs, so the level each theorem depends on can be read from the layout
   (§ Measuring the levels).
4. **The tactics become theorems.** The Agda solvers (`CayleyAssoc`, `GroupoidSolver`,
   `Normaliser`, `PastingDSL`) are plain terms: a syntax of expressions, an interpretation
   and a soundness proof. In Unit each is stated once as a lemma and cited by name. The
   normaliser's `sound` becomes Mac Lane's coherence theorem for the 2-wild Cat: two
   parallel composites of associators and unitors are equal.
5. **Internal coherences from contractibility.** Composition of morphisms inside a
   category C, and its laws, are not given by equations. They come from contractible types
   of fillers, `Fun(Δⁿ, C)` over a spine, obtained from the Segal condition for all n. This
   continues the principle of the Agda proof of Lemma 26: Δⁿ is posetal, so being a
   pushout is a property and the induction carries no coherence data.
6. **Writing.** Each file follows `seg/WRITING.md`:
   - the informal proof comes first, in the file comment;
   - each notion has one name;
   - "by definition" facts are `refl` lemmas;
   - a construction is locked after its characterising lemmas;
   - every file is checked with `--opened`, and is under 1 s.

## The axioms and the layout of segments

`All.seg` nests the segments as follows (a sketch, not yet checked):

```
module Theory (univ) (images) (surjections) {
  fe = ... ;  import <foundations of sag/sip> ;
  -- level 1: the wild category Cat
  module Wild (Cat : U l+) (Map : Cat -> Cat -> U l)
              (comp) (idMap) (assoc) (id-l) (id-r) {
    import Whiskering ; import Cayley ; ...
    -- the structure axioms, stated with level-1 data only
    module Structure (cat-univalence) (one) (terminal)
                     (pb ...) (Fun) (ev) (exp-is-equiv)
                     (I) (I-ob) (I-mor-order) (I-char ...)
                     (segal-is-equiv) ... {
      import <files using no coherence above level 1> ;
      -- level 2: pentagon and triangle
      module Coh2 (pentagon) (triangle) {
        import MacLane ; import Pasting ; ... import Lemma26 ;
        -- level 3, added when a proof first needs it
      } ;
    } ;
  } ;
} ;
```

The axioms, with the Agda postulates and the SW numbering:

| Axiom | Agda postulates | SW |
|---|---|---|
| wild category Cat, level 1 | `Cat Map comp idMap comp-assoc comp-id-l comp-id-r` | SW1 (1)–(4) |
| level 2 coherences | `pentagonator Id-triangle2` | footnote to SW6 |
| univalence of Cat | `cat-univalence` | SW2 |
| terminal category | `𝟏c terminal` | part of SW3 |
| pullbacks | `pb pb-pr₁ pb-pr₂ pb-comm pb-is-equiv` | SW11 |
| exponentials | `Fun ev exp-is-equiv` | SW3 |
| the interval | `𝕀 𝕀-ob 𝕀-mor-order 𝕀-char-inverse 𝕀-char-rinv 𝕀-char-linv` | SW4, SW5 |
| Segal | `segal-is-equiv` | SW6 |
| Rezk | `rezk` | SW7 |
| I detects equivalences | `𝕀-detects-equiv` | SW9 |

In the port (M7) both are parameters of `Structure`, declared after `Invertible`:
`rezk C a : isContr ((b : Ob C) * ObIso C a b)` (univalence of objects; the Agda
form, idtoiso an equivalence, is the theorem `rezk-idtoiso`), and
`I-detects-equiv f : isEquiv (post-comp f I) -> isIso f`.  The statement of `rezk`
needs invertibility, hence composition, which is defined at level 1 from the
Segal axiom (`Composition`).

Three further Agda postulates are listed as axioms in its README but may be provable:
`𝕀-hom-contr` (𝕀 has one nontrivial arrow), and `segal-coface-01`, `segal-coface-12` (the
spine edges of the Segal comparison agree with the geometric cofaces). In the port they
start as parameters of `Structure`, marked as candidates, and the aim is to prove them
from the others. SW8 (triangulation of the square), SW10 (full subcategories), SW12
(coproducts), SW13 (the classifier of left fibrations) and SW14 (pushouts) are not used
before the Segal condition for all n. They are added when first needed.

Universe levels: `Cat : U l+` and `Map C D : U l` (Cat is locally small), as in the Agda
version (`Type (𝓤₀ ⁺)`, `Type 𝓤₀`).

## Files, in dependency order

The order of the Agda modules, with their size in lines. Unit names drop the Agda directory
prefixes. Possible name clashes with the foundation files (for example `Category`,
`Functor`, `Universal`) are avoided.

- **M0 Foundations.** `Spartan` (281) is replaced by links to `sag/sip` (`Prelude`, `Paths`,
  `Axioms`, `FunExtUA`, `Truncation`). Only what is missing is added:
  - `HLevels` (170): only the parts not already in the Prelude;
  - `SigmaEquiv` (140): Σ-equivalence lemmas;
  - `Retracts` (61): retracts of equivalences.
- **M1 The wild category.**
  - `WildCat` (from `CatAxioms`, 131): whiskering and the reassociator, as definitions over
    the parameters of `Wild`;
  - `CatCoherence` (from `Coherence`, 218);
  - `Cayley` (from `CayleyAssoc`, 81, a lemma);
  - `GroupoidWords` (from `GroupoidSolver`, 164, a lemma);
  - `MacLane` (from `Normaliser`, 335): the coherence theorem;
  - `Pasting` (from `PastingDSL` 171 and `PastingTest` 61).
- **M2 Structure.**
  - `HigherCat` (137), `Constructions` (119), `Pullbacks` (145), `Exponentials` (132),
    `ExpEval` (50), `UnitIso` (81);
  - `Product` (1,701): products from pullbacks over the terminal category, with the
    pentagon for products, `prod-pent-C`, which is proved in the Agda version;
  - `Interval` (1,241).
- **M3 Order and faces.** `OrdCompare` (35), `FaceOrd` (29), `OrdComb` (353), `LastEdge`
  (63), `Segal` (339), `FaceMap` (67), `FaceOrdCompat` (96), `IntervalPosetal` (109),
  `PosetalCore` (247), `FunIPosetal` (228), `Posetal` (28).
- **M4 Squares and pushouts.** `Square` (102), `SquareAlg` (203), `ConeUnit` (140),
  `ConeComp` (401), `ConeNat` (415), `TimesI` (749: −×I preserves pushouts).
- **M5 Lemma 26.** `FaceTop` (52), `FaceTopProof` (81), `PushoutBase` (53),
  `SimplexRetract` (574), `SimplexRetractValues` (317), `SquareGeom` (479), `PushoutDef`
  (31), `PushoutProof` (107), `SegalGeom` (403), `Lemma26` (from `Pushout.agda`, 207):
  `lemma26-square : (n : Nat) -> is-pushout-square (Sq (suc n))`.
- **M6 Segal for all n (new).** From Lemma 26 and `segal-is-equiv`, by induction on n:
  `Fun(Δⁿ, C)` is equivalent to the type of chains of n composable morphisms. Then
  n-simplices with a given spine form a contractible type. Composition of morphisms is the
  centre for n = 2, and associativity (n = 3) and the unit laws are instances. Composition
  is locked after these characterising lemmas.
- **M7 Fully faithful functors (new).** Results 33–39 of the notes:
  - `Hom-map-comp` and `id-hom-is-inv`, proved from M6;
  - `is-inv-mor-is-prop`, with invertibility defined as "postcomposition is an
    equivalence", following Step A of `HANDOFF-fullyfaithful-coherence.md`;
  - Rezk and 38 as parameters;
  - Remark 39 last.

The Agda total for M0–M5 is about 11,200 lines. The `Zigzag/`, `OLD/` and `unused/`
directories are not ported.

## Measuring the levels

Finite ambient coherence proposal (2026-11-01):
[`../../doc/hcat-ambient-segal.tex`](../../doc/hcat-ambient-segal.tex)
([PDF](../../doc/hcat-ambient-segal.pdf)) formulates a 5-restricted
semi-Segal presentation of Cat, compared with Sattler–Wärn and
Capriotti–Kraus. It isolates the degree-5 endpoint comparison and the
compatibility with the existing `hcomp-assoc` needed to derive `hpent`.
This is a mathematical proposal, not a checked replacement for `Coh3`:
the finite extension and its comparisons remain to be constructed.
`All.seg` and the homology development retain their current parameters.

The subsequent [internal refactor experiment](../hcat-segal/README.txt)
constructs new composition and associativity from finite horn fillers and
derives their pentagon. The existing homology theorem files, including
Mayer–Vietoris and spheres, check against that interface through relative
links. See the [refactor note](../../doc/hcat-segal-refactor.pdf).
This takes internal semi-Segal data as parameters; constructing them from
the original ambient axioms remains open. The original `hcat` proof files
and its assumption of `hpent` are unchanged.

The finite internal semi-Segal inputs are now adopted as axioms for
continuing homology in the sibling root. The
[homology continuation note](../../doc/hcat-segal-homology.pdf) records
homotopy/equivalence invariance, identification of group units with zero
classes, and a Mayer–Vietoris tail of groups through degree zero.
The sibling root now proves degree-zero multiplicativity, additivity of
the existing final boundary, comparison of
the structural boundary with the looped direct boundary, and naturality
for supplied coherent maps of representable squares. It checks:
114 modules, 2876 declarations, 0 failures; fresh `--opened` 3.13 s.
The boundary proof constructs a connecting arrow to the suspension and
identifies the existing boundary, under the chosen equivalences, with
its pointed loop map. No new axioms beyond the explicit parameters.
Constructing the representable cube from maps of type pushouts remains
open. The new `hcat-spectrum` root assembles the existing
Eilenberg–MacLane spaces into coefficient Omega-spectrum data
(36 modules, 1001 declarations, 0 failures); the categorical model and
ordinary-homology comparison remain to be constructed.

By the layout, a theorem needs at most the level of the segment it is checked in. After
M5 and after M7, record for each main theorem the innermost segment it needs, by moving
it outward until it no longer checks. The questions are:

- whether Lemma 26, Segal for all n and the results of M7 stay at level 2;
- whether the action of functors on morphisms, natural transformations or Yoneda need
  level 3.

The answers go in a table here.

Levels after M5 (by the layout of All.seg; each Coh2 entry uses the pentagon
or the triangle directly, or a lemma that does):

| Theorem | Innermost segment | Why |
|---|---|---|
| naturality of the reassociator, xch, Lemma 25 | Wild | level-1 data only |
| products, pmc, ipe, prod-path-eq | Structure | level 1 |
| construction-20, I-char, I-hom-contr, Segal comparison | Structure | level 1 |
| Delta-posetal, posetal-hom-is-set | Structure | level 1 |
| segal-coface-01/12, retract-SSk (S(n+2) < S(n+1) x I) | Structure | level 1 |
| triangle1, triangle3, Mac Lane coherence | Coh2 | pentagon |
| prod-pent-C | Coh2 | pentagon (pi1 factor), unit-loop (pi2 factor) |
| sq-cone-pre-id | Coh2 | triangle2, triangle3 |
| sq-comparison-natural, sq-cone-pre-comp, retract of a pushout | Coh2 | pentagon |
| times-I-preserves | Coh2 | prod-pent-C |
| base-Sq1 | Coh2 | pentagon at (h, face 1, eval-pt-inv, I1) |
| lemma26-square | Coh2 | all of the above |

So Lemma 26 needs level 2 and nothing of level 3.  The geometry (retract-SSk,
the cofaces, posetality) is level 1; level 2 enters through the algebra of
cones and products.

Levels after M7 (by the layout of All.seg):

| Theorem | Innermost segment | Why |
|---|---|---|
| chains, universal spine, spine (Chains) | Structure | level 1 |
| composition `composite`, its witness/filler lemmas, comparison with `comp-mor` | Structure | Segal axiom at n = 2 only |
| `spine-two` (the n = 2 spine is the boundary map) | Structure | level 1 (posetality of Delta 2) |
| `is-inv`, `is-inv-prop`, `is-ff`; statement of `rezk` | Structure | level 1 |
| `Hom-map-of-comp` (Hom-map of F o G) | Coh2 | pentagon |
| `Hom-map-id` (functors preserve identities, with endpoints) | Coh2 | pentagon, compose-naturality3, triangle3 |
| `Hom-map-gen` | Coh2 | triangle2 |
| `Chain-map-of-comp` | Coh2 | Hom-map-of-comp |
| `pushout-is-equiv` for all n | Coh2 | Lemma 26 |
| `segal-all` (Segal for all n), `filler-contr` | Coh2 | Lemma 26, Chain-map-of-comp |
| `Hom-map-comp` (functors preserve composition) | Coh2 | Hom-map-of-comp |
| unit laws `hcomp-unit-r/l` | Coh2 | Hom-map-id, Hom-map-gen |
| associativity `hcomp-assoc` | Coh2 | segal-all at n = 3, Hom-map-comp |
| Lemma 35, `rezk-idtoiso`, Lemma 37, Remark 39 (both directions) | Coh2 | unit laws, associativity |
| FibreInclusion, CommutingLoops, LoopDifference, PullbackSource/Difference | Structure (lexical only) | type theory; no Cat parameter used |
| HomologyDouble, HomologyFibreSource, HomologySequence | Stable inside WithPentagon | existing hpent, copowers and stability; no further coherence |

So Segal for all n, composition with its laws, and the results 33-39 need
level 2 and nothing of level 3.  Composition itself is level 1; level 2 enters
through the action of functors on morphisms with their endpoints (Hom-map),
because Ob C is not a set.

## Validation

From `unit/`:

```
./segc sag/hcat all
SEG=$(cabal list-bin exe:seg); "$SEG" sag/hcat/All.seg --opened
./segc sag/hcat stop
```

Each file is under 1 s. Each milestone is recorded below with its check figures.

## Expected difficulties

- **Implicit arguments.** The Agda code relies on them heavily. Unit fills omitted
  arguments only by one-way matching, so many arguments will be written. This is
  presentation, not mathematics.
- **Paths between paths.** The cost of 2-paths shows in the `--opened` reports. A
  declaration that opens more than its text says is split at the step the text states.
- **Product.agda.** It is the largest file (1,701 lines) and carries the pentagon for
  products. It should be read before it is ported, to see whether the product structure
  can be characterised by its universal property and locked early.
- **The three candidate postulates.** If they cannot be proved, they stay as axioms, and
  the README says so.

## Status

- 2026-11-01: positive-degree Mayer--Vietoris sequence assembled in
  `HomologySequence` (54 lines), with all three repeating positions
  exact and every arrow a homomorphism of the EXISTING abelian groups.
  It uses the usual i_*, j_*, u_*-v_* and ONE structural boundary;
  consecutive pieces agree definitionally. The positive tail ends at
  H_1(X), with no exactness claim at that final term. `FibreInclusion`
  retains the projected path; `PullbackSource` and `PullbackDifference`
  prove source exactness for the same boundary as `PullbackFibre`.
  `CommutingLoops` removes basepoint compatibility obligations when
  loops at the target commute. `HomologyDouble` therefore obtains
  double-loop naturality from L-nat without a higher law for L.
  `HomologyFibreLegs` now uses one lemma for both legs (49 lines).
  Remaining: degree-zero extension and categorical naturality of the
  assembled sequence; H3a still open, hpent still assumed. No new
  axioms: univ, images, surjections and the existing Cat, copower,
  zero-object, suspension and stability parameters are unchanged.
  Validation: changed, 14 modules, 0 failures, 0.70 s; full server check,
  169 modules, 3978 declarations, 0 failures, 14.46 s. Fresh full
  --opened: 3978 declarations, 0 failures, 17.44 s. All new files under
  1 s. Both mathematical notes and PDFs updated.

- 2026-11-01: structural reconstruction of the exact sequence.
  `FibreSequence` proves exactness and homomorphism laws for the same
  maps pi_1(fib f) -> pi_1(Y) -> pi_1(W). `FibreTower` iterates pointed
  fibre inclusions by ordinary recursion. `FibreTowerMaps` and
  `FibreTowerNaturality` propagate one specified pointed square to
  commuting group squares at every stage; no further coherence inputs.
  `PullbackFibre` retains the equivalence of the fibre of the product
  projection with the loop space of the apex, over the boundary map.
  `HomologyFibre`, `HomologyFibreLegs`, and `HomologyFibreExact` then give
  ONE connecting homomorphism H_(n+2)(X) -> H_(n+1)(C), exact at its
  target with the existing i_* and j_*, for every n >= 0. These are the
  existing abelian groups. Comparison with the old boundary is not
  needed for this result. Remaining: identify the other tower stages
  with the conventional grading and difference map, degree zero, and
  supply pointed input squares for categorical naturality. The full
  conventional natural LES is not yet proved. No new axioms: Theory
  still has univ, images, surjections; the existing Cat, copower and
  stability parameters, including hpent, are unchanged. H3a remains open.
  Validation: changed, 131 modules, 0 failures, 17.12 s; server all,
  159 modules, 3651 declarations, 0 failures (cached). Fresh full
  --opened check: 3651 declarations, 0 failures, 16.91 s. Every new
  module is under 1 s. Mathematical note and PDF updated.

- 2026-11-01: completed the missing Mayer--Vietoris exactness position
  under the existing hpent. `MayerVietorisExact.exact-p` and
  `difference-zero` prove ker(delta) = im(u_* - v_*) at H_(n+1)(X), for
  the original boundary and chosen group structures. `delta-point-path`
  proves that this boundary is pointed. `ZeroCoherence` and `ConeZero`
  supply the basepoint compatibility using hpent. The generic pullback
  path, exactness and naturality theorems are in Theory (no Cat).
  `MayerVietorisLoop` separately constructs a homomorphism
  H_(n+2)(X) -> H_(n+1)(C) by looping the preceding pointed boundary.
  Agreement with the original boundary at the next degree, its
  additivity, degree-zero homomorphisms and categorical naturality
  remain open. In particular, the new map has not been substituted into
  the exactness results. The comparison is stated as a type, not added
  as an axiom-system parameter. H3a and hpent are unchanged.
  Validation: changed passes; full check, 149 modules, 3349 declarations,
  0 failures, 14.03 s. Fresh --opened check of the nine new modules and
  Pi0/Pi0Maps: 359 declarations, 0 failures, 0.75 s. Each new module is
  under 0.2 s in the full check. Mathematical note updated accordingly.

- 2026-11-01: positive-degree homomorphisms proved under the existing
  hpent. Pi0Maps proves the pointed loop-map and transport lemmas;
  HGroupMaps applies L-nat to the existing HGroups.LoopGroup structures.
  hmap-mul/one/inverse hold in every positive degree, and hmap-id/comp
  in every degree. Degree-zero and connecting homomorphisms remain open.
  H3a progressed but is NOT finished: HomTripleShort and
  HomTripleLongCells normalize the actual short path and all five long
  steps; HomTripleNormalize places them over one morphism path and
  reduces HMOC3 to two explicit endpoint equations. Their derivation
  from k5 remains open, followed by the triangle, composition-witness,
  associator-preservation and 4-simplex steps. No parameters were added;
  hpent remains assumed and the chosen associator is unchanged.
  Validation: fresh --opened check of the six new files, 227 declarations,
  0 failures, 2.14 s; changed, 10 modules, 0 failures, 1.44 s;
  full server check (with cached results), 140 modules, 3090 declarations,
  0 failures, 9.27 s. Each new file checks in under 1 s.
- 2026-11-01: HomEqMap.MapEq.naturality proves the action of Hom-map on
  Hom-eq including both endpoint cells. HomFunctorPaths provides the
  functor-path and endpoint-transport comparisons with explicit forms.
  These use Structure only. HomTriple (Coh2) constructs both actual paths
  of HMOC3 using the existing Hom-map-of-comp terms; their equality type
  is stated as Triple.Coherence, without an assumed proof. Identifying
  their normalized endpoint pastings with k5 is still open, as is hpent.
  No parameters were added and the existing associator is unchanged.
  Validation: fresh --opened check, 72 declarations, 0 failures, 0.50 s;
  changed passes; full check, 134 modules, 2863 declarations, 0 failures,
  12.16 s.
- 2026-11-01: continued the k5-to-hpent comparison with the existing
  HomFunctor proof terms fixed. HomCompEndpoints.Normal.form-explicit
  expresses Hom-map-of-comp at arbitrary endpoints as explicit pentagon
  and naturality pastings (Coh2). HomEqCoerce.Coerce.naturality computes
  endpoint transport of Hom-eq paths and their 2-cells (Structure).
  The corresponding Hom-map action and the full HMOC3 equation remain
  open; hpent has not been discharged. No new parameters were added.
  Fresh --opened check: 53 declarations, 0 failures, 0.43 s; changed
  passes; full check: 131 modules, 0 failures, 11.59 s. Each new file
  checks in under 0.25 s.
- 2026-11-01: attempt to derive hpent from k5; hpent is still open.
  Added HomEqHigher (comparison of paths with endpoint witnesses),
  EquivIndBeta (computation of homotopy extension, by univalence),
  PentagonReduction (the chosen associator on spines; reduction to
  4-simplex spines), and K5Hom (equal Hom paths from the actual k5
  endpoint pastings). The last lemma uses Coh3; the reduction uses Coh2;
  the two generic comparison lemmas use only the type theoretic
  foundations. No new axiom-system parameters were introduced.
  Identification with the existing Hom-map-of-comp pastings, followed
  by coherence of composition witnesses, remains necessary.
  Validation: fresh --opened check of the four files, 56 declarations,
  0 failures, 0.47 s; changed passes and server all reports 129 modules,
  2738 declarations, 0 failures (cached results). Homology continues to
  use its existing hpent parameter.
- 2026-11-01: witness transport, compatible with the concurrent H4-H5 work.
  `WitnessTransport` proves transport along squares, identity/pasting laws,
  and coherent uniqueness when the target vertical map is an equivalence.
  `CopowerPost` applies this to postcomposition, including comparison of
  successive and direct postcomposition as full witnesses. Its projection
  is not yet identified with the specified associator of D.
  Levels: WitnessTransport uses only the type theoretic foundations;
  CopowerPost uses Coh2 and the existing copower parameters, with no new
  axioms and no use of hpent or stability. Both are integrated alongside
  the other work's Stable segment without changing its parameters.
  Changed/all validation snapshot: 122 modules, 2545 declarations,
  0 failures, full check 11.24 s. New modules: 80 declarations total,
  each module at most 0.02 s; fresh --opened check: 0 failures, 0.25 s.
- 2026-11-01: universal-witness coherence experiment for homology.
  `UniversalWitness.globes-contr` and `Witness.coherence` prove coherent
  uniqueness at every finite globular path dimension; `CopowerWitness`
  retains beta compatibility in identity and composition comparisons.
  `CompWitness` isolates the general postcomposition calculation, and
  `ExcisionAssoc.rt-assoc` now applies it. See DESIGN-HOMOLOGY.md for the
  scope and the remaining ambient-coherence problem.
  - Levels: UniversalWitness is imported in Structure (uses only the type
    theoretic foundations); CopowerWitness uses Coh2 and the copower
    parameters; CompWitness is in Coh2 with the internal pentagon as an
    explicit theorem argument; its excision instance still uses hpent.
  - Validation snapshot: changed and all pass; all checked 108 modules,
    2089 declarations, 0 failures in 9.59 s. The four witness/excision
    modules also pass a fresh --opened check: 94 declarations, 0 failures,
    0.56 s. The new modules each check in at most 0.31 s. The full snapshot
    includes concurrent additions elsewhere in hcat.
- 2026-10-31: design written. No code yet.
- 2026-10-31: M0-M5 done.  `./segc sag/hcat all`: 74 modules, 1407 declarations,
  0 failed, 6.2 s; every file under 1 s (largest ProductPentagonR 0.88 s), every
  declaration under 1 s.  `lemma26-square : (n : Nat) -> is-pushout-square (Sq (suc n))`.
  - Of the three candidate postulates, all are proved: `I-hom-contr`
    (IntervalPosetal), `segal-coface-01` and `segal-coface-12` (SegalCoface).
    The Structure axioms are those of the table above plus `segal-is-equiv`.
  - Solvers are theorems: Cayley.solveR, GroupoidWords.solveG, MacLane (full
    Mac Lane coherence, coh/composeA-coh).
  - Restructured (statements kept): the cone lemmas (ConeAlg: comparison as
    postcomposition of a base cone; ConeComp: one generic leg lemma), the
    product pentagon (frames, ProductPentagon*), TimesI (transpose ev o (k x I)),
    SegalGeom (one reshuffle lemma).  Not ported: the PastingDSL aliases (one
    name per notion), Zigzag/, OLD/, unused/.
  - Not yet done: M6, M7.
- 2026-10-31: M6 and M7 done.  `./segc sag/hcat all`: 88 modules, 1674
  declarations, 0 failed, 7.2 s; every new file under 0.2 s.
  - M6.  `HChain C n x` (chains glued at the last vertex), `univ-chain n` (the
    spine of Delta n), `spine-total C n s` = s applied to it.
    `SegalAll.segal-all : (n : Nat) (C : Cat) -> isEquiv (spine-total C n)`,
    by induction with Lemma 26 (via the square `Sq-I` with I for Delta 1, a
    retract of `Sq`) and `Chain-map-of-comp`; `filler-contr`: the fillers of
    a chain are contractible.  Composition (`Composition.composite`, `hcomp`)
    is the centre of the fillers at n = 2 (`spine-two`), locked after
    `composite-witness` and `composite-filler`; `composite-agrees` compares
    it with `Segal.comp-mor` on every 2-simplex.  `hcomp-unit-r/l`
    (degenerate 2-simplices of I), `hcomp-assoc` (segal-all at n = 3; the
    two composites agree in the posetal Delta 3, and the 3-simplex
    preserves composition).
  - M7.  Invertibility is condition 3 of Definition 34 (postcomposition is an
    equivalence), so `is-inv-prop` is free.  The three Agda postulates
    Hom-map-comp, id-hom-is-inv, is-inv-mor-is-prop are theorems
    (`CompLaws.Hom-map-comp`, `FullyFaithful.id-is-inv`,
    `Invertible.is-inv-prop`).  New parameters of Structure: `rezk`,
    `I-detects-equiv`.  Proved: Lemma 35 `ff-reflects-inv`, `rezk-idtoiso`,
    Lemma 37 `ff-emb`, Remark 39 `ff-surj-iso` (fully faithful and
    surjective on objects, with truncated surjectivity, gives an
    isomorphism) and its converse `iso-ff`, `iso-surj`.
