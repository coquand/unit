# Contraction and transpose proof improvements

Date: 2026-10-25. The mathematical results use the existing ring assumptions
and uniform checker. No axioms or checker rules were added. Both files
begin with their informal proofs; the expected computations are recorded
in `PCC2-TRANSPOSE.opens`. The interfaces introduced during this refinement
have a separate `PCC2-IMPROVEMENTS.opens` specification.

## Changes to the proof structure

Scalar transposition now uses the named vector coordinate and matrix entry
accessors from `Alternating` and `Determinant`. Their defining equations
are proved once by reflexivity and the accessors are locked.
`Determinant.act-coordinate` gives the coordinate formula for matrix
action. `transpose-entry` states how transposition exchanges entries.

Consequently `vdot-transpose` has an explicit intermediate sum of
coordinates before it applies the action equation. Distribution, exchange
of the two finite sums, and reassociation of scalar factors then proceed
by the existing named lemmas. The proof opens neither matrix action nor
coordinate/entry accessors. Its residual openings are types.

The grade-involution argument is checked once as the generic
`ExteriorUniversal.grade-natural`: an algebra map with odd generator
images commutes with alpha, by uniqueness on generators.
`Determinant.Map.value-alpha` applies this to the exterior map.
`value-zero` follows directly from its named additivity law. The transpose
and naturality proofs now cite these laws instead of rebuilding algebra
composites and unpacking their preservation laws.

`ExteriorUniversal.ext-precomp-value` names the pointwise inverse equation
already used to construct `ext-precomp`; the equality of bundled maps is
assembled from this component. `ExteriorContr` names the value of the
standard generator extension and its identity and graded equations.
`gen-commute` transports those equations. The contraction proof uses this
result directly; its local `Graded` reconstruction has been removed.

For the contraction pairing, left multiplication by a generator is named
`left-wedge`. Its value, rank-zero and successor equations are stated at
its definition, then the operator is locked. The pairing's generic
`dot-pair` and `dot-pair-right` equations are stated once in
`ExteriorDuality`. `contract-pair` explicitly writes the contraction's
pair, its three scalar summands, their reassociation, and the reconstruction
of the generator product. It uses these characterisations by name.
`right-pair` explicitly applies `left-wedge-value` at its interface.

The mixed-identity component calculation explicitly opens `left-wedge`
locally, then locks it again. Six redundant local definitions of the two
components, generator, contraction, generator multiplication and scalar
pairing have been removed; it uses the shared operations and component
accessors under their original names. Its component claims and
intermediate second product component `y1` remain named proof steps.

## Measurements, including the new interfaces

All counts include repeated openings. Before and after counts for the two
proof files come from matched standalone `--only` checks, with dependencies
trusted in both cases. Before reports are preserved in
`pcc2-audit/contraction-before.opened` and
`pcc2-audit/transpose-before.opened`; the current reports are
`PCC2-CONTRACTION.opened` and `PCC2-TRANSPOSE.opened`.

| Declaration | Before | After |
|---|---:|---:|
| `vdot-transpose` | 376 | 37 |
| `vdot-sum` | 45 | 8 |
| `act-transpose-value` | 22 | 15 |
| `Natural.unit` | 37 | 2 |
| `contract-pair` | 137 | 68 |
| `MixedStep.top-result` | 52 | 20 |
| `MixedStep.bottom-result` | 45 | 13 |
| `MixedStep.result` | 186 | 142 |

The earlier intermediate figure of 53 for `contract-pair` came from a
combined check also checking Duality. The matched standalone measurement
is 68. Checking dependencies can populate evaluation caches, so reports
with different module selections should not be treated as identical
measurement conditions.

| Defined comparison slice | Openings |
|---|---:|
| Both original proof files | 2,644 |
| Both revised proof files | 1,473 |
| All added or relocated shared interface declarations, charged once | 584 |
| Revised files plus those shared interfaces | 2,057 |

The shared charge includes **all** of `coordinate` / `coordinate-value`
(7), `entry` / `entry-value` / `act-coordinate` (27), `value-zero` /
`value-alpha` (24), `alpha-hom` / `grade-natural` (225),
`ext-precomp-value` (26), the four standard-extension declarations (241),
and the two dot-pair equations (34). The new left-wedge declarations and
`transpose-entry` are already included in the revised proof-file totals.
Their own costs have not been omitted or counted twice.

These are an explicitly defined proof-and-interface slice, not a claim
about all dependency checking or runtime. In particular other existing
dependency declarations, including the revised assembly of `ext-precomp`,
are outside this comparison. The interface reports use separate standalone
checks, recorded as `pcc2-audit/*-interfaces.opened`.

## What remains visible

The specifications exclude inherited carrier encodings from the
mathematical clients. Extras remain visible; this is not a claim that
the checking-as-reading audit is completely clean.

- `vdot-transpose` now has only `Fin` (31), `Vec` (4) and `Mat` (2)
  openings. Previously these were 28, 262 and 83 respectively, with three
  additional openings of action/sum. The finite-index function interface
  still needs work.
- `contract-pair` has `Ext` (60), `Vec` (4), `dot` (2), `contract` (1)
  and `isSet` (1). The two mathematical definitions open in its rank-zero
  case. Its displayed pairs increase carrier decoding relative to the
  preceding compressed proof (38 `Ext`), while reducing repeated vector
  decoding (52 to 4). The explicit equation helpers add further work:
  this particular subtree alone is not claimed to have a net saving.
- Algebra-map packaging remains visible at the generic construction
  boundary: `grade-natural` has 122 openings; the standard extension's
  identity and graded components have 106 and 110. These costs are
  charged above. They have not disappeared merely because downstream
  proofs use the named components.
- `MixedStep.result` still expands the recursive product, contraction and
  componentwise addition to assemble its two component proofs. Its
  informal proof and annotation explicitly state those computations.

Thus the refinement both improves the proof's decomposition and reduces
the measured slice, but leaves concrete representation work to address.
No conclusion about fidelity follows solely from these counts.

## Validation

The focused checks report **64 contraction declarations** and **66
transpose declarations**, with zero failures. The full integrated check
reports **1,890 declarations, zero failures** (0.81 seconds locally),
saved in `PCC2-FULL.checked`.

From the Unit repository:

```sh
cabal exec seg -- sag/exterior/All.seg
cabal exec seg -- sag/exterior/All.seg --only ExteriorVectorContraction --opened --opens sag/exterior/PCC2-TRANSPOSE.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorTranspose --opened --opens sag/exterior/PCC2-TRANSPOSE.opens
cabal exec seg -- sag/exterior/All.seg --only Alternating --opened --opens sag/exterior/PCC2-IMPROVEMENTS.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorUniversal --opened --opens sag/exterior/PCC2-IMPROVEMENTS.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorContr --opened --opens sag/exterior/PCC2-IMPROVEMENTS.opens
cabal exec seg -- sag/exterior/All.seg --only Determinant --opened --opens sag/exterior/PCC2-IMPROVEMENTS.opens
```

Environment: base revision `19d44d8cb1b4d9ee83a704e67ad046ba13919c8d`
with the in-progress changes, Darwin arm64, GHC 9.6.7, existing Cabal build.
The final transposition, naturality and adjugate statements retain their
mathematical content; `contract-pair` uses the named operator whose
`left-wedge-value` equation gives its former generator-product expression.
