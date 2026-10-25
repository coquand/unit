# Coordinate duality proof audit

Audited `ExteriorDuality.seg` against `/Users/coquand/CANONICITY/seg/WRITING.md` on 2026-10-25. The file's informal proof describes its recursive coordinate pairing, signed complementary map, perfect top-product pairing, and representation of linear forms. The proof has been expanded to state the component and inclusion steps that the initial report exposed. The annotation is `ExteriorDuality.opens`.

## Repairs made

The initial report repeatedly opened `Ext` merely to recover the types of projections. Its largest occurrences were 156 in `star-pair`, 137 in `dot-add`, 118 in `representation`, and 96 in each of `dot-scale` and `dot-alpha`. These were repeated representation work rather than additional algebraic arguments.

`ExteriorModel` now declares the single shared accessors `first` and `second`, their `first-pair` / `second-pair` equations, and the reconstruction equation `components`. These five declarations cost 20 openings in total and are checked once. The accessors become opaque after characterisation. Duality explicitly reopens them during its component inductions and locks them again afterward. Its primitive `dot`, `star`, and `unstar` definitions are unchanged; existing computational clients remain compatible.

The linear-form proof also omitted intermediate steps. They are now explicit named facts:

- `linear-add` and `linear-scale` project the two laws in `Linear`.
- `left-add`, `left-scale`, `right-add`, and `right-scale` establish the linearity equations for the coordinate inclusions once, using addition-zero and scaling-zero.
- `split-add` reconstructs a vector as the sum of its two coordinate inclusions. Its proof writes the intermediate point `(first x,second x)` and applies the shared reconstruction equation.
- `dot-left` and `dot-right` evaluate pairing with an inclusion using the named zero-pairing and addition-zero laws.

The inclusions are made opaque after these characterisations. `left-lin` / `right-lin`, `representation`, and `dual-dot` now apply these facts by name. No duplicate component projection or pair-equality alias was introduced. Homogeneous proofs were updated to reuse the same upstream accessors; their former local front/back copies were removed.

## Measurements

| Declaration | Original `Ext` openings | Revised `Ext` openings | Original total openings | Revised total openings |
|---|---:|---:|---:|---:|
| `dot-add` | 137 | 9 | 154 | 40 |
| `dot-scale` | 96 | 8 | 109 | 29 |
| `dot-alpha` | 96 | 8 | 118 | 38 |
| `star-pair` | 156 | 8 | 176 | 36 |
| `left-lin` | 44 | 6 | 77 | 9 |
| `right-lin` | 44 | 6 | 77 | 9 |
| `representation` | 118 | 25 | 149 | 40 |
| `dual-dot` | 93 | 9 | 108 | 16 |

These are per-declaration counts including repetitions, not counts of distinct names. Across the whole Duality file, all openings decrease from 1505 to 646, including its nine inclusion helper declarations and the two dot-pair equations added for the contraction proof. Charging the entire shared accessor package to this file gives 666 openings. Thus the reduction is not merely a transfer of the old work into new helper declarations. The local check time remains approximately 0.13–0.14 seconds; no runtime improvement is claimed.

## Reading the remaining report

The opening specification follows the definitions invoked in the informal proof; it does not permit the bodies of any algebraic lemmas. `--opens` reports no extra opening and no allowed-but-unused opening.

`Ext` still opens to identify the scalar carrier in dimension zero and the pair carrier in a successor dimension. `first` and `second` open only where the component representation is explicitly used. Opening `dot`, `star`, `unstar`, and `dual` is the stated recursion in their inductive proofs. Opening `ezero`, `eadd`, `eneg`, `escale`, `alpha`, `emul`, and `top` is the corresponding component equation described in the text.

In particular, the eight carrier openings in `star-pair` accompany the explicitly written expansion of `dot(star x,y)` and of the top coefficient of the product. The proof then applies `dot-alpha`, its induction hypotheses, commutativity of addition, and `top-add` by name. None of those theorem bodies is opened.

The 25 carrier openings in `representation` remain mostly type formation and identification of the recursive pair with its scalar base case. The only mathematical definitions opened there are `dual`, `dot`, `Linear`, and `escale`, together with the two component accessors. The scalar clause writes `x=x*1` and uses named linearity and multiplication commutativity; the pair clause uses named reconstruction and inclusion linearity. Neither inclusion nor addition is unfolded there anymore. `Linear` itself is opened for the pair-shaped evidence in the zero-dimensional comparison and the recursive applications. `isSet` appears once at the ring-laws module instance to identify its supplied sethood predicate; it performs no algebraic computation.

The final `dot-inj`, `wedge-inj`, and `represent` proofs open no mathematical constructions beyond the stated linearity predicate in `represent`. Their remaining openings are decoding the carrier's type; the mathematical uniqueness argument uses the named inverse and representation laws.

## Reproduction and limits

From the Unit repository:

```sh
cabal exec seg -- sag/exterior/All.seg --only ExteriorDuality --opened
cabal exec seg -- sag/exterior/All.seg --only ExteriorDuality --opens sag/exterior/ExteriorDuality.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorModel --opens sag/exterior/ExteriorDuality.opens
cabal exec seg -- sag/exterior/All.seg
```

The Duality check passes with 50 declarations, 0 failed. The Model check passes with 33 declarations, 0 failed; the five accessor declarations are included in `ExteriorDuality.opens`, while older Model declarations are outside this audit. The full integrated check passes with 1890 declarations, 0 failed, in 0.81 seconds locally. Homogeneous is separately rechecked and audited after sharing the accessors: 44 declarations, no extra openings.

This audit changes proof decomposition and access to the existing representation, not the mathematical statements. No axioms, transpose/contraction changes, or checker changes were made. Unfolding agreement is a diagnostic for this informal proof, not a proof of semantic fidelity.

Environment: repository base revision `19d44d8cb1b4d9ee83a704e67ad046ba13919c8d` with shared in-progress files; existing Cabal build, GHC 9.6.7, Darwin arm64. Name-only split comparison retained.


`dot-pair` and `dot-pair-right` are the generic defining equations used by the revised contraction proof; each opens definitions 17 times. Their costs are included above and in `PCC2-TRANSPOSE-AUDIT.md`.
