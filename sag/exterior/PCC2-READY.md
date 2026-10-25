# PCC2: main results available to other developments

Status: **PCC2 Theorems 1 and 13 are proved**, including the fixed-cardinality
subset sum and the actual replacement-column determinants. The scalar
Cramer statement is exactly **CFFR Proposition 8.3**, with the names of the
two vector families exchanged. These theorem interfaces are stable for
other terminals to use read-only.

Full validation through `All.seg`: **2,090 declarations, zero failures**,
0.97 seconds locally; see `PCC2-FULL.checked`.

## Consumer interface

For `Rg : Ring[l].CRing`, `setR : Prelude[l].isSet Rg.R`, let
`a : Fin p -> Vec n` be the p replacement vectors and
`B : Fin n -> Vec n` the n original columns. Instantiate once:

```
module PS = ExteriorPluckerSylvester[l].Over[Rg,setR] ;
module T = PS.At[n,p,a,B] ;
```

- **`T.cramer`** is PCC2 Theorem 1 / CFFR Proposition 8.3:
  `det(B) * (a_1 wedge ... wedge a_p)` is the sum of the replacement
  determinant times the product of the selected original columns.
- **`T.plucker-sylvester`** is PCC2 Theorem 13: contraction of the original
  n-fold product by the p-fold replacement product equals the sum of the
  corresponding contractions of the replaced n-fold products.
- `PS.interior`, `interior-pair`, `interior-degree`, `interior-unique`,
  `interior-add`, `interior-scale`, `interior-volume`, and `interior-top`
  provide Definition 10 and the contraction/volume identification.
- `PS.Homogeneous` and `PS.star-isomorphism n p r h`, where
  `h : p+r=n`, give the complementary-degree star equivalence. Its
  linearity is provided by the existing `ExteriorDuality.star-add/scale`.

`T.S.value` is the sum over exactly the binary subset indices of cardinality
p. It takes a family `(i : Index n) -> count(i)=p -> Ext n`; terms at other
indices are zero. `T.subset-a` transports the list length along that equality.
`T.replacement-determinant` is the determinant of the constructed replaced
matrix; `T.replacement-volume` is its ordered n-fold generator product.
`T.Repl.product i B` is the ordered product of the original columns selected
by i. These are independently defined constructions, not theorem inputs.

Link the current files read-only. After the existing homogeneous and
transpose development and their dependencies, import:

```
import ExteriorCramerIdentity ;
import ExteriorReplacement ;
import ExteriorPluckerSylvester ;
```

`All.seg` gives the complete checked dependency order. In particular use
the current `ExteriorHomogeneous.seg`, which now supplies degree
preservation, orthogonality, and complementary-degree star/unstar laws;
and the current `ExteriorAlgebra.seg`, which supplies `zero-scale`.

## Supporting results and proof route

`ExteriorCramerIdentity.At[n,B]` provides `map-adj` (the second adjugate
composition identity), `adj-degree`, `adj-coeff`, `complementary-minor`
(PCC2 Lemma 5 in the coordinate-minor convention), and the all-subset
Cramer expansion. The first composition identity is in `ExteriorAdjugate`.
The transpose lemmas and determinant transposition are in `ExteriorTranspose`.

`ExteriorReplacement` constructs the increasing selected positions and
column replacement, proves that selected columns are replaced and
complementary columns retained, and identifies the resulting coefficient
with the replacement determinant. The sign calculation uses
`basis(I)*star(basis(I))=omega`, proved by its degree and top coefficient.
No generic matrix, fraction field, division or HIT is introduced. The
existing univalence/replacement assumptions are unchanged.

The standalone arbitrary homogeneous-form isomorphism of Proposition 3
and the reverse-implication package of Remark 14 are not exported as
separate declarations. The main theorem proofs use the constructed full
perfect pairing, complementary-degree results and named star inverse
laws directly. Likewise the general shuffle formula of Lemma 2 is not a
separate interface; the complementary volume identity needed by the
coefficient proof is proved. These scope distinctions do not leave an
assumption in either main theorem.

## Unfolding audit

Each new file starts with its informal proof. Expected-opening files and
saved reports are `PCC2-CRAMER.opens/.opened`,
`PCC2-REPLACEMENT.opens/.opened`, and `PCC2-PLUCKER.opens/.opened`.

The final `T.cramer` proof opens definitions 20 times, all in the types
`Summand`, `Index`, `Vec`, and `Mat`. The final `T.plucker-sylvester` proof
opens them 29 times, in the same four encodings. Neither unfolds a
mathematical construction or theorem body. The largest declaration in
the replacement file is `select-position`, with 92 openings, including
its stated recursive count/position clauses. Residual representation
costs remain visible in the reports; no claim of a completely clean
whole-library reading audit is made.

Reproduction from the Unit repository:

```
cabal exec seg -- sag/exterior/All.seg
cabal exec seg -- sag/exterior/All.seg --only ExteriorCramerIdentity --opened --opens sag/exterior/PCC2-CRAMER.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorReplacement --opened --opens sag/exterior/PCC2-REPLACEMENT.opens
cabal exec seg -- sag/exterior/All.seg --only ExteriorPluckerSylvester --opened --opens sag/exterior/PCC2-PLUCKER.opens
```

The focused runs check 28, 52 and 78 declarations respectively, with zero
failures; dependencies are trusted in these runs and checked by the full
entry point. The full entry point uses the standard uniform checker with
name-only split comparison. Environment: Darwin arm64, GHC 9.6.7, existing
Cabal build, in-progress workspace changes.
