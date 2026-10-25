# Second adjugate identity and Cramer expansion

`ExteriorCramerIdentity.seg` starts with the informal proof for every
declaration. It adds the second composition identity, two coordinate
expansions of that identity and the complementary-coefficient formula.
It uses the existing exterior algebra, adjugate and transposition
theorems. It introduces no new axiom or desired-identity parameter, and
does not change the checker or the replacement-based foundation.

`complementary-minor` additionally proves PCC2 Lemma 5 in the coordinate
minor convention:

```
coeff_i(Adj(A) basis_j)
  = epsilon_i epsilon_j coeff_(complement j)(phi_A(basis_(complement i))).
```

This follows from the coefficient formula by applying `star-basis` to
both selected basis vectors. The two signs move through the existing
linear and scalar laws; symmetry and `dot-basis` extract the remaining
coordinate. No signed-complement or minor definition is unfolded in
this proof.

The second identity is proved by moving the exterior map and adjugate
across the coordinate pairing. The existing first identity for the
transposed matrix then applies. Equality of the two determinants and
nondegeneracy finish the proof. The proof needs no determinant
cancellation, field assumption or new double-transpose conversion.

`adj-degree` proves that the adjugate preserves every homogeneous
degree. For an index whose size differs from the input degree,
`adj-coeff` and the existing homogeneous `cramer-coeff-zero` theorem
give a zero coordinate of the image. The existing `support-degree`
theorem then yields homogeneity. This supplies the degree-p adjugate
from the already constructed full-algebra map without a new definition
or extra assumption.

The coefficient formula has the displayed intermediate pairing
`dot(star(Adj(A)x),star(basis_i))`. Star is an isometry, and star-pair
identifies that value with the top product to which the existing
adjugate characterisation applies. The only mathematical definition
opened in this proof is the existing adjugate `form` at its displayed
value.

`cramer` is the all-subset formula

```
det(A) x = sum_i top(x * phi_A(star(basis_i))) phi_A(basis_i).
```

No homogeneous support assertion is assumed in this sum. The later
application restricts the sum using independently proved support
results. This file consequently supplies a required algebraic identity,
not the final replacement-column Plücker–Sylvester statement by itself.

## Unfolding report

`PCC2-CRAMER.opens` lists the intended openings: `LinearMap` when its
two laws are supplied, `Support` when supplying the coordinate and
inequality arguments, and `form` when its value is displayed. The
remaining declarations use no mathematical definition by computation.
The specification does not whitelist the carrier encodings merely
because the report observed them.

The report `PCC2-CRAMER.opened` shows:

| Declaration | Openings beyond the stated mathematical ones |
| --- | --- |
| `map-adj` | 30 `Vec`, 30 `Mat`, 12 `Ext`, 3 `isSet` |
| `adj-linear` | none |
| `adj-expansion` | 2 `Ext` |
| `cramer-source` | 3 `Vec`, 3 `Mat`, 2 `Ext` |
| `adj-coeff` | 2 `Index`, 2 `Ext`, 1 `isSet`, 1 `Mat` |
| `adj-degree` | 3 `isSet`, 2 `Index`, 2 `Deg`, 2 `Ext`, 1 `Not` |
| `cramer-target` | 3 `Vec`, 3 `Mat`, 2 `Ext` |
| `cramer` | 5 `Index`, 2 `Vec`, 2 `Mat`, 2 `Ext` |
| `complementary-minor` | 4 `Index`, 2 `isSet`, 1 `Ext` |

These are reported carrier, index, degree-predicate and logical-premise
decoding costs. They remain
visible audit defects; the report is not represented as having zero
extra openings. There are no openings of the exterior-map computation,
the adjugate construction, finite-sum recursion or transposition.
The proof cites those constructions by their existing names and laws.

## Validation

Focused reproduction through the integrated entry point:

```
cabal exec seg -- sag/exterior/All.seg --only ExteriorCramerIdentity --opened --opens sag/exterior/PCC2-CRAMER.opens
```

This checks 28 declarations with zero failures. Dependencies are
trusted in this focused run. `All.seg` includes the new import, and
the temporary entry point has been removed. The parent is responsible
for the full development check after the final theorem additions.
