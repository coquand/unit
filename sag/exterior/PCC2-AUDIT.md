# PCC2 writing and unfolding checkpoint

Audit date: 2026-10-25. This addresses the missing informal proofs, missing
design update, and missing unfolding checks identified during the PCC2 work.
It is a completed diagnostic pass with repairs, not a claim that all the
checking-as-reading requirements have been met.

All seven new mathematical files now begin with their informal proofs.
`DESIGN.md` records what has been constructed and what remains of the
paper. New mathematical extensions were paused for this work. No new
axioms or checker changes were introduced.

## Reports and their scope

| Files | Expected openings | Recorded checks / explanation |
|---|---|---|
| Model, universal inclusion and exterior-map interfaces | `PCC2-INTERFACES.opens` | `PCC2-CORE.opened` |
| `ExteriorDuality.seg` | `ExteriorDuality.opens` | `PCC2-DUALITY.opened`, `PCC2-DUALITY-AUDIT.md` |
| `ExteriorCoordinates.seg` | `ExteriorCoordinates.opens` | `PCC2-CORE.opened`, `PCC2-COORDINATES.checked` |
| `ExteriorBasis.seg` | `ExteriorBasis.opens` | `PCC2-CORE.opened`, `PCC2-BASIS.checked` |
| `ExteriorAdjugate.seg` | `ExteriorAdjugate.opens` | `PCC2-CORE.opened`, `PCC2-ADJUGATE.checked` |
| `ExteriorHomogeneous.seg` | `ExteriorHomogeneous.opens` | `PCC2-HOMOGENEOUS.opened`, `PCC2-HOMOGENEOUS-AUDIT.md` |
| Contraction and transposition | `PCC2-TRANSPOSE.opens` | `PCC2-CONTRACTION.opened`, `PCC2-TRANSPOSE.opened`, `PCC2-TRANSPOSE-AUDIT.md` |

`--opened` reports multiplicities as well as distinct names. Counts below
include repetitions. `--opens` compares the observed definitions with
those stated by the informal proof; its command succeeding does not mean
there were no extras. The saved reports retain those diagnostics.

The coordinate, basis, adjugate, duality, homogeneous and new-interface
specifications have no extra openings in their recorded runs. The new
refinement specification `PCC2-IMPROVEMENTS.opens` deliberately retains
carrier extras at generic algebra-map and extension boundaries. Their text
and annotations explicitly describe the recursive `Ext` and `Index`
representations and, where used, column matrices, coordinate vectors,
linearity predicates and the supplied ring sethood. Accounting for those
names does not remove their repeated cost. The contraction/transposition
specification deliberately excludes inherited carrier encodings and
continues to flag them. Thus the specifications have different scopes;
the number of flagged extras is not a measure for comparing these files.

## Repairs in the common interfaces

The first report showed repeated decoding of the same algebra-map
carrier through `Determinant.Lam`, `ExteriorUniversal.Lam`,
`ExteriorAlgebra.algebra`, `AlgHom` and nested projections. The value of
`Determinant.Map.phi` and its preservation laws are now named once with
explicit `Ext n` types. `value-eprod` proves preservation of ordered
products by induction. New clients use these components, and pass the
bundled `phi` where a universal property requires an algebra map.
`phi` is opaque after its generator characterisation. This last lock
also prevents `phi` and the universal extension `ext` from opening while
checking the component accessors themselves.

The inclusion `iota` similarly has its preservation laws named at its
construction. `iota-hom` packages these same laws; `iota-eprod` follows
by induction. The selected-basis proof uses this interface instead of
repeatedly decoding `iota-hom`. `Determinant.Product` no longer introduces
another alias for the exterior map. Redundant local pair-equality and
component aliases have also been removed.

Shared `first` and `second` accessors and their defining/reconstruction
facts now belong to `ExteriorModel`. Recursive component proofs use
these names and explicitly open them locally. The accessors are locked
after their characterisations. This substantially reduces the repeated
carrier decoding caused by raw pair projections. The duality report
also records the named inclusion linearity and decomposition steps.

| Selected declaration | Initial openings | Revised openings |
|---|---:|---:|
| `ExteriorDuality.dot-add` | 154 | 40 |
| `ExteriorDuality.star-pair` | 176 | 36 |
| `ExteriorDuality.representation` | 149 | 40 |
| `ExteriorCoordinates.dot-basis` | 96 | 59 |
| `ExteriorCoordinates.dot-sum` | 58 | 34 |
| `ExteriorBasis.lift-prod` | 143 | 13 |
| `ExteriorBasis.image-product` | 99 | 22 |
| `ExteriorBasis.top-map` | 285 | 60 |
| `ExteriorAdjugate.At.form-linear` | 359 | 15 |
| `ExteriorAdjugate.At.adj-map` | 231 | 51 |
| `ExteriorTranspose.Natural.step` | 658 | 60 |

These are local declaration counts, not totals for all old and new
interfaces together. `PCC2-CORE.opened` includes the new interfaces' own
costs. The duality report gives a whole-file comparison including its
new helpers: 1,505 to 666 openings when the entire shared component
package and the new dot-pair equations are charged there. The homogeneous report charges its new local
interfaces and shared components explicitly. No runtime improvement or
proof-fidelity conclusion is inferred from these reductions.

## Outstanding work exposed by the audit

Repeated decoding still matters even when a file checks quickly.
The subsequent refinement is detailed in `PCC2-TRANSPOSE-AUDIT.md` and
`PCC2-IMPROVEMENTS.opens`. Named coordinates and entries reduce
`vdot-transpose` from 376 to 37 openings; it now opens only `Fin` (31),
`Vec` (4), and `Mat` (2). The contraction pairing now states its component
calculation explicitly and uses named generator multiplication; it opens
68 definitions in the matched standalone check, versus 137 before.
Its 60 carrier openings remain visible. The former `Graded` and
`map-alpha` reconstructions have been replaced with components named at
their generic constructions. Their source costs are included in the
refinement report, together with all added helper costs.

The two proof files decrease from 2,644 to 1,473 openings; charging all
584 added or relocated shared-interface openings gives 2,057 for this
specified slice. This is not a whole-development or runtime comparison.
The generic algebra-map and extension components still decode carriers,
and `MixedStep.result` still performs its explicitly stated recursive
assembly. Those remaining costs are recorded, rather than erased by
allowing more names in the specifications.

The main mathematical results are now complete: `PCC2-READY.md` records
Theorems 1 and 13, the CFFR Proposition 8.3 consumer interface, their final
unfolding reports, and the precise remaining intermediate export scope.
The independent `PCC2-REPLACEMENT` and `PCC2-PLUCKER` specifications retain
representation extras while confirming that both final theorem proofs
unfold no mathematical construction.

## Reproduction and validation

Run from the Unit repository. The `.checked` and `.opened` files record
the corresponding commands' standard output.

```sh
cabal exec seg -- sag/exterior/All.seg
cabal exec seg -- sag/exterior/All.seg --only ExteriorModel --only ExteriorUniversal --only Determinant --only ExteriorCoordinates --only ExteriorBasis --only ExteriorAdjugate --opened --opens sag/exterior/PCC2-INTERFACES.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorCoordinates --opens sag/exterior/ExteriorCoordinates.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorBasis --opens sag/exterior/ExteriorBasis.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorAdjugate --opens sag/exterior/ExteriorAdjugate.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorDuality --opened --opens sag/exterior/ExteriorDuality.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorHomogeneous --opened --opens sag/exterior/ExteriorHomogeneous.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorVectorContraction --opened --opens sag/exterior/PCC2-TRANSPOSE.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorTranspose --opened --opens sag/exterior/PCC2-TRANSPOSE.opens
```

The full integrated check reports **2,090 declarations, zero failures**
(0.97 seconds locally), saved in `PCC2-FULL.checked`. Focused `--only`
runs trust other imported modules and are used to isolate diagnostics;
the full check checks all their dependencies too.

Environment: base revision `19d44d8cb1b4d9ee83a704e67ad046ba13919c8d`
with the in-progress changes described here, Darwin arm64, GHC 9.6.7,
existing Cabal build. The checker retains name-only split comparison.
