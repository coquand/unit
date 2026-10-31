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
