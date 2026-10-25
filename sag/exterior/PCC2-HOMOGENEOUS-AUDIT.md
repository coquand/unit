# Homogeneous-coordinate proof audit

Audited `ExteriorHomogeneous.seg` against `/Users/coquand/CANONICITY/seg/WRITING.md` on 2026-10-25. Its head now contains the complete informal proof, including the recursive representation, each induction case, and each algebraic intermediate point. The accompanying annotation is `ExteriorHomogeneous.opens`.

## Scope and results

The checked mathematical interfaces are:

- `deg-prop`, `coeff-support`, and `support-degree`: homogeneous membership is a proposition and is equivalent to vanishing of coefficients outside the specified degree.
- `complement`, its involution, and `count-complement`: the complementary subset and its cardinality equation.
- `epsilon-square`, `coeff-star`, and `star-basis`: signed complementation has a unit sign and the expected coefficient and basis formulas.
- `deg-mul`, `deg-scale`, `top-vanish`, and `top-product-vanish`: multiplication adds degrees; scalars preserve degree; a homogeneous element contributes to the top coefficient only in the top degree.
- `map-degree` and `phi-degree`: a linear map preserves specified homogeneous degrees when its basis images do, and every exterior map of a matrix preserves degree.
- `star-basis-degree`, `top-complement-vanish`, and `cramer-coeff-zero`: complementary basis degree and exact vanishing of the off-degree coefficients in the Cramer expansion.
- `dot-degree-vanish`: orthogonality of distinct homogeneous degrees.
- `homogeneous-dot-inj`: nondegeneracy with test vectors restricted to the same degree.
- `star-degree`, `star-degree-reflect`, and `unstar-degree`: star and unstar exchange degree p and degree r whenever p+r=n.
- `DecNat.dec` and addition cancellation supply the elementary natural-number decisions and index equalities used in these proofs.

No adjugate-degree theorem has been added here; the complementary-basis case is sufficient for the Cramer support restriction, and general star degree exchange is checked separately below. No axioms or checker changes were made.

## Investigation and repair

The first report exposed repeated decoding in `deg-mul`: `Ext` opened 134 times, `Deg` 68, `shift` 14, and `emul` 12. This was more work than its informal phrase “decompose the homogeneous pair and multiply” expressed.

The proof now states this work explicitly and names its interfaces: the upstream `ExteriorModel.first` and `ExteriorModel.second` project the model components, `deg-left` / `deg-right0` / `deg-rightS` extract the degree evidence, `deg-pair0` / `deg-pairS` assemble it, and `mul-rec` states multiplication's recursive equation by reflexivity. `deg-mul` uses those names. The projection accessors matter: introducing only degree wrappers initially increased carrier decoding; using `first` / `second` removes that repeated decoding at applications.

| Openings in `deg-mul` | Before | After |
|---|---:|---:|
| `Ext` | 134 | 42 |
| `Deg` | 68 | 36 |
| `shift` | 14 | 0 |
| `emul` | 12 | 2 |
| All definitions, including repetitions | 262 | 111 |

The six local interface declarations open definitions 45 times in total. Thus the multiplication proof together with its local interfaces has 156 openings, compared with the original 262. The shared upstream accessor package (two accessors, their two pair equations, and reconstruction) costs another 20 openings checked once; charging its entire cost here gives 176. This is a check of the proof's decomposition, not a runtime claim.

The remaining `Deg`, `deg0`, `plus`, and two `emul` openings in `deg-mul` implement its explicit zero-dimensional cases and degree-index equations. Its `Ext` openings are residual decoding of the recursive carrier, including formation of pairs and application of the named interfaces. No algebraic theorem body is opened there.

Two redundant aliases were also removed: the copied `pair-eq` name is replaced by the original `ExteriorAlgebra.pair-eq`, and the copied `top-zero` lemma is replaced by the existing `Adjugate.Over.top-zero`. The unused FunExt module instance was removed. The local front/back copies were replaced by the upstream first/second accessors; those accessor definitions have a single name shared with ExteriorDuality. `twist`, `epsilon`, `first`, `second`, and `complement` become opaque after their characterisations; downstream proofs use their named equations.

## Other openings and their mathematical meaning

The annotations were written from the expanded informal proof, not by treating every observed name as an allowable theorem body. The following representation dependencies are explicit in that proof:

- `Index` and `Ext` decode the sum-of-subsets and pair-of-exterior-elements representations. The largest remaining such counts are `Index` 42 in `star-basis`, 37 in `alpha-basis-scale`, while `Ext` now opens 8 times in `coeff-star`. These declarations perform the corresponding two recursive cases; no other construction is being identified by conversion.
- `Deg`, `deg0`, and `shift` implement the four degree clauses written in the text. `Support`, `Not`, `coeff`, and `count` are opened exactly in the support induction and its converse.
- `basis`, `escale`, `alpha`, `eneg`, `star`, `epsilon`, `twist`, and `complement` are opened in the explicitly stated recursive sign and complementary-basis arguments. `alpha-basis-scale` has 96 openings in total; they belong to these four operation definitions and the two recursive representations. Its zero components have the intermediate point zero written in their equality chains.
- `isProp` identifies the proposition predicate in the proposition proofs. `isSet` identifies the supplied sethood of the ring when applying ring/module instances; it does not prove an algebraic fact by conversion. It appears in `Over.L`, `deg-prop`, `coeff-support`, `coeff-star`, and `top-vanish`. The latter three use module instances or identity lemmas whose sethood parameter is named by a different imported interface.
- `top` is opened only in the induction proving top-vanishing. The final `top-product-vanish` opens only `Ext` twice: it applies `deg-mul` and `top-vanish` by name. `deg-scale` uses the named `emb-mul` equation and the zero clause of `plus`; no ring or exterior theorem body is opened.

`--opens` reports no undeclared openings for every annotated declaration, and no unused allowed opening. The recursive representation costs remain visible and explained; this report does not claim that equal unfolding reports prove mathematical fidelity.

## Degree preservation and Cramer support

The file's informal proof now also gives the complete basis-expansion argument for `map-degree`. Decidable equality splits each subset term according to whether its cardinality is the source degree. In the equal case the basis-image hypothesis and `deg-scale` apply. In the unequal case `coeff-support` makes the scalar zero. `sum-degree` assembles the result and `CO.map-expansion` identifies it with the map's value. `phi-degree` supplies `BA.image-degree` to that generic theorem.

The first proof of the zero term used the generic packaged algebra law `AL.In[UP.Lam m].scale-zero-l`. Its report opened `Alg` 14 times, `algebra` 10 times, and `Lam` 10 times: 34 openings of the algebra representation. This was unnecessary decoding at this step. An initial repair wrote the mathematical common points scale(0,y)=emb(0)*y=0*y=0 through typed model laws. The shared `ExteriorAlgebra.zero-scale` theorem is now available and the current proof applies it directly. `MapDegree.term` has 9 openings instead of 42, with no algebra package or mathematical theorem body opened. Its statement and proof are shared rather than reintroduced locally.

`star-basis-degree` transports the degree of a scaled complementary basis along the already proved `star-basis` equation. `top-complement-vanish` compares the two equations p+count(i^c)=n and count(i)+count(i^c)=n. Right addition cancellation would force count(i)=p, contradicting the hypothesis; `top-product-vanish` therefore applies. `cramer-coeff-zero` supplies the image under phi_A of star(basis_i), whose degree is supplied by the two preceding named degree theorems. It gives exactly the scalar appearing in the all-subset Cramer formula, without assuming an adjugate degree theorem or using transposition.

The added opening specifications follow these explicit steps. The natural-number decision opens only `Not`, and left addition cancellation opens only `plus`; right cancellation opens no definition. `sum-degree` opens `Index`, its named finite `sum`, and `eadd` for the binary sum clause. The remaining openings in the generic map proof are `Index`, `Deg`, `Support`, `Not`, `Ext`, and the supplied ring's `isSet`, plus `LinearMap` at the module's evidence type. No coefficient, basis, map, or named theorem body is unfolded there. `phi-degree` opens `Deg`, `Mat`, `Index`, `Ext`, and `LinearMap`, all type/predicate representations. The final `cramer-coeff-zero` opens only `Mat`, `Index`, and `Ext` once each: all mathematical work is checked by named applications.

The new mathematical theorem bodies are opaque after their statements, including the internal term/result proofs. No dependency on `ExteriorTranspose` or `ExteriorCramerIdentity` was introduced. The local `DecNat` is necessary because the existing `Koszul.DecNat` is defined downstream of Homogeneous; upstream clients can now share this earlier decision instead of introducing further copies.

## Orthogonality and the general complementary-degree isomorphism

The informal proof now gives orthogonality of distinct degrees by the named coefficient sum `CO.dot-sum`. At each subset index, `DecNat.dec` decides whether its count equals the first degree. Support kills the second coefficient in the equal case and the first coefficient in the unequal case. `scalar-sum-zero` then sums the zero products. This uses no recursive expansion of dot or of the exterior values.

`complement-count` and `complement-count-reflect` use left and right cancellation in the existing complement cardinality equation. With p+r=n, they respectively turn count_i=p into count(i^c)=r and reflect the latter equality back to the former. `star-degree` supplies this transported complementary basis degree to the already proved `map-degree`, using star's named addition and scaling laws. Conversely, `star-degree-reflect` applies `coeff-star` at an off-degree index. The reflected cardinality equation ensures that the complementary coefficient of star(x) is zero. `epsilon-cancel-zero` cancels the sign using epsilon-square=1, with each associativity/unit/zero point written in the proof. The named `support-degree` converse then proves that x has degree p. `unstar-degree` combines this reflected theorem with the named inverse law star-unstar.

The new audit reports no mathematical theorem body or computational sign opened. Its principal counts are:

| Declaration | Definitions opened, including repetitions |
|---|---:|
| `scalar-sum-zero` | `Index` 29, `Sum.sum` 4 |
| `DotDegree.term` | `Not` 7, `Support` 5, `Index` 2 |
| `DotDegree.result` | `Ext` 8, `Index` 2 |
| `dot-degree-vanish` | `Ext` 2 |
| `complement-count`, `complement-count-reflect` | `Index` 2 each |
| `star-degree` | `Deg` 3, `Index` 2, `Ext` 2, `LinearMap` 1 |
| `epsilon-cancel-zero` | `Index` 2 |
| `star-degree-reflect` | `Not` 5, `Support` 5, `Index` 2, `Deg` 2, `Ext` 2 |
| `unstar-degree` | `Deg` 3, `Ext` 2 |

Here the `Index`/`Ext` counts decode the subset and carrier types; `Support`/`Not` allow application of the support implications; `Deg` and `LinearMap` identify the stated degree and linearity evidence. The scalar sum's two recursive clauses are explicitly described in the proof. In particular, `star`, `unstar`, `epsilon`, and every named degree theorem remain unopened in these applications. All new mathematical theorem bodies and the internal term/result proofs are opaque afterward. The opening specification has no unexplained or unused entry.

## Nondegeneracy with homogeneous test vectors

`homogeneous-dot-inj` compares two degree-p elements that have equal dot pairings against every degree-p test vector. Coordinate extensionality reduces equality to each subset coefficient. A cardinality decision either gives a degree-p basis vector (transported from `basis-degree`), when the hypothesis and two `dot-basis` equations give the coefficient equality, or makes both coefficients zero by `coeff-support`.

Its report contains exactly `Support` 4, `Ext` 4, `Index` 3, `Deg` 3, and `Not` 1. These decode the support implication, carriers, indices, and degree predicate described in the text. No pairing, basis, support theorem, or mathematical theorem body is opened. The theorem is opaque after proof.

## Reproduction

From the Unit repository:

```sh
cabal exec seg -- sag/exterior/All.seg --only ExteriorHomogeneous --opened
cabal exec seg -- sag/exterior/All.seg --only ExteriorHomogeneous --opens sag/exterior/ExteriorHomogeneous.opens
```

Both checks pass: 85 declarations checked, 0 failed (other imported files are trusted by `--only`). The measured whole-file checking time was about 0.16–0.18 seconds with diagnostics. This is a local incremental audit, not a full audit of dependencies. The parent has integrated these files into `All.seg`; the temporary independent entry point was deleted. The integrated `All.seg` check also passes: 1890 declarations, 0 failed (0.81 seconds locally). This task did not edit `All.seg`.

Environment: repository base revision `19d44d8cb1b4d9ee83a704e67ad046ba13919c8d` with shared in-progress files, GHC 9.6.7, Darwin arm64, the existing Cabal build. Name-only split comparison was retained.

