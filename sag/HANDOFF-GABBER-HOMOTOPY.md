# Handoff: formalise the homotopy lemma (gabber-recollement.tex, Lemma 3.5)

Source: `unit/doc/gabber-recollement.tex`, Lemma 3.5 (checked carefully on
paper, 2026-11-02). Read `../seg/WRITING.md` before writing any `.seg` file.
Proposed home: a new directory `sag/gluing-homotopy/`.

## Statement

Let `A` be a commutative ring and `a, b : A` comaximal. Let
`g ∈ GL_M(A_ab)` and `ε(T) ∈ GL_M(A_ab[T])` with `ε(0) = I`. Then there are
`β ∈ GL_M(A_b)` and `α ∈ GL_M(A_a)` with

    g · ε(1) = β · g · α        (images in A_ab).

(Consequence, not part of this task: `P_{g ε(1)} ≅ P_g` for the glued module.)
Represent `GL` as pairs `(C, D)` with `C D = I = D C`.

## Proof (LQ XVI.3.1–3.4, then assembly)

1. **LQ 3.1.** If `P ∈ B[X]`, `P = 0` in `B_S[X]` and `P(0) = 0`, then
   `P(sX) = 0` for some `s ∈ S`. This is mostly in
   `horrocks/PolynomialClearing.seg` (the kernel part).
2. **LQ 3.2.** If `P ∈ B_S[X]` and `P(0) = 0`, then `P(sX)` comes from
   `B[X]`. This is the clearing part of `PolynomialClearing`.
3. **LQ 3.3.** The matrix version of 3.1, applied entrywise.
4. **LQ 3.4.** For `C(X) ∈ GL_p(B_S[X])` there are `s ∈ S` and
   `U(X,Y) ∈ GL_p(B[X,Y])` with `U(X,0) = I` and `U = C(X+sY) C(X)^{-1}`
   over `B_S`. The proof writes `E(X,Y) = C(X+Y)C(X)^{-1} = I + Σ E_j(X) Y^j`,
   clears denominators with `Y ↦ s₁Y`, does the same for the inverse, and
   uses 3.3 (base ring `B[X]`, variable `Y`) to make the lifts inverse over
   `B`.
   - Two variables are needed: the uniformity in `X` is what lets the
     assembly choose `x, y` after `N`. A one-variable version runs into a
     circular dependency, because `N` would depend on `y` and `y` on `N`.
   - Take `B[X,Y]` to be `(B[X])[Y]` (`Poly` over the ring `B[X]`).
   - If `U` works for `s`, then `U(X, s'Y)` works for `ss'`.
5. **Assembly.**
   - Apply 3.4 with `B = A_a`, `S` the powers of `b`, `C = ε`. This gives
     `U₁`.
   - Apply 3.4 with `B = A_b`, `S` the powers of `a`, `C = φ := g ε g^{-1}`.
     This gives `U₂`.
   - Use a common exponent `N` and write `1 = a^N x + b^N y`.
   - Set `β := U₂(b^N y, x)` and `α := U₁(0, y)`. Using `ε(0) = I`, the image
     of `α` is `ε(b^N y)`. Then
     `g ε(1) = φ(1) g = [φ(1) φ(b^N y)^{-1}] g ε(b^N y) = β g α`.
   - Whitehead's identity (gabber-recollement Lemma 3.6(1)) is a separate,
     later step.

## Existing pieces to reuse (check them before writing)

- `horrocks/MonoidLocalization.seg`, `MonoidFractions.seg`,
  `MonoidLocalizationMap.seg`: `A_S` for any monoid `S`, and its map from `A`.
- `horrocks/PolynomialClearing.seg`: LQ 3.1/3.2 for single polynomials, with
  common denominators for finite families.
- `polynomial/Substitution.seg` (`X ↦ p`), `polynomial/Universal.seg`,
  `PolynomialMap`: evaluation, `T ↦ T+sY`, and base change along `B → B_S`.
- Matrices: `exterior/Determinant.seg` (`Mat n = Fin n -> Vec n`, `mmul`,
  `idm`) and `exterior/MnAlgebra.seg`. Pick one representation and keep it.
- The identification `(A_a)_b ≅ A_ab ≅ (A_b)_a` may be the main bookkeeping
  cost. Either define `A_ab` as `(A_a)_b` and transport only once, or
  state the lemma with abstract maps `A_a → C`, `A_b → C` satisfying the
  needed localisation properties.

## Rules

- Every single checker run must take under 60 s (memory
  `shell-timeout-one-minute`). Use `./segc DIR changed` (memory
  `seg-load-cost`).
- Lock each construction right after its characterising lemmas
  (`seg-opacity-principle`).
- No ring solver: write ring identities by hand (`no-ring-solver`).
- Report the theory parameters used; never say "no axioms".

## Status (2026-11-02): DONE, checked

`sag/gluing-homotopy/` (`../segc sag/gluing-homotopy all`: 45 modules, 0.34 s).
The main statement is `Homotopy.Over.Lemma.theorem`. Theory parameters: `univ` (through `fe`,
`propUA`), `images`, `surjections`, the same as `horrocks`; no new axioms.

The statement is more general than the one above. It holds for any commutative square
`A -> A_a -> C`, `A -> A_b -> C`, where `A_a -> C` is *localising at b* and
`A_b -> C` is *localising at a* (`Localising.seg`: clearing denominators plus killing the
kernel by powers). So the identification `(A_a)_b = (A_b)_a` is never needed. A concrete
instance with `MonoidLocalization` has not been written.

Files, in the order of the proof:
- `Bounds`: monotone exponent bounds, with a common bound for finite or matrix families.
- `Localising`: definition of a localising map.
- `PolynomialLocalising`: `R -> C` localising at s implies `R[X] -> C[X]` localising at s
  (LQ 3.1/3.2, without rescaling the variable).
- `ConstantTerm`: `value0`, `tail`, `p = p(0) + X tail p`, and X is regular.
- `Rescaling`: `X |-> cX`, evaluation, and base change, compared by the universal property.
- `MatrixMap`, `Unipotent`, `Conjugation`: matrix algebra.
- `Lift`: LQ 3.4 in the form used: inverse F, F' over C[X] with F(0) = 1 lift to inverse
  G, G' over R[X] with `G |-> F(s^k X)`.
- `Comaximal`: powers of comaximal elements are comaximal.
- `Homotopy`: the assembly.

A simplification over the paper proof: the two lifts need not share one exponent N. Lifting
gives b^k1 and a^k2, and comaximality of a^k2 and b^k1 directly gives x and y. So the step
"U(T,s'Y) works for ss'" is not needed.

## Status (2026-11-02, later): Lemma 3.6(1) at the matrix level DONE, checked

`DiagonalProduct.Over.Lemma.theorem` (`../segc sag/gluing-homotopy all`: 48 modules, under
0.5 s; same theory parameters). Same hypotheses as `Homotopy`, plus inverse M x M pairs
(g, g') and (h, h') over C; it gives inverse 2M x 2M pairs beta over A_b and alpha over A_a with
`diag(g,h) = beta diag(gh,1) alpha` (images in C).
- `Blocks`: Fin (m+n) = Fin m + Fin n (`injl`, `injr`, `side`, `join`), `sum-plus`,
  block matrices `blk a b c d` (opaque after `at-ll` .. `at-rr`), `Equal` (equality by
  blocks), `block-mul`, `blk-one`, `map-blk`.
- `Whitehead`: `u`, `lo`, `diag`, `u-left`/`lo-left`, inverses, `diag-mul`, `whitehead`
  (u h' l(-h) u h' u(-1) l 1 u(-1) = diag(h',h), multiplied out from the right), and the
  homotopy `word c X1..X6` (every block times c): inverse `word'`, `word-zero`, `word-one`,
  `map-word`.
- `DiagonalProduct`: eps(T) = word T h' (-h) h' (-1) 1 (-1) over C[T]; eps(0) = 1,
  eps(1) = diag(h',h); then `Homotopy` for diag(gh,1).
Concrete instance DONE: `Localisations.seg` (with `LocalizationIdentities`, `MonoidFractions`,
`MonoidLocalization`, `MonoidLocalizationMap` copied unchanged from `horrocks`; 53 modules,
0.51 s). `Step[x,y,w,xy=w]`: A_x -> A_w (localisations at powers) is localising at y.
`Instance[setA,a,b,comaximal]` takes A_a -> A_ab <- A_b and gives
`HomotopyAt[N].theorem` (Lemma 3.5) and `DiagonalAt[M].theorem` (Lemma 3.6(1), matrix level).
Still open: the module level (P_g + P_h = P_gh + M), which needs glued modules and K_0.

## Status (2026-11-02, evening): Lemma 3.6(1) at the module level DONE, checked

`StableSum.Over.Lemma.theorem` (`../segc sag/gluing-homotopy all`: 65 modules, 0.64 s from a
fresh server; same theory parameters, no new axioms). Hypotheses: those of `DiagonalProduct`
plus `ka : A -> A_a localising at a`, `kb : A -> A_b localising at b`. Conclusion: merely an
isomorphism of A-modules `P_g + P_h ~ P_gh + A^M` (no K_0; step 5 not needed).
Concrete instance: `Localisations.Over.Instance[..].StableAt[M].theorem`, with
`Localisations.Over.Inclusion[x].localising` (A -> A_x localising at x).
Modules are qcqs's `SerreModule` (symlinked with `SerreModuleMaps`, `SerreModuleProducts`,
`RingMaps`); sums are `SerreModuleProducts.Pair`, A^M is `SerreModuleProducts.Over` of
`regular`. New files, in the order of the proof:
- `ModuleIso`: `Iso[Md,Nd]` (a `SerreModuleMaps` Hom over the identity + inverse map),
  `make`, `identity`, `inverse` (the inverse is linear), `compose`, `Sum` (iso of sums).
- `Vectors`: `Vec = Fin N -> R`, `act X u`, `act-mul`, `act-one`, `act-cancel`; `Map`: `map-act`.
- `Glued`: `Glue[g]` = P_g = {(u,v) | jb v = g ja u} as a submodule of A_a^M + A_b^M
  (`glued`, accessors `left`/`right`/`member`, `point`, `ext`); `Invariance[g,k,beta..,e]`:
  `P_k ~ P_g` when k = beta g alpha.
- `VectorBlocks`: halves of vectors over Fin(M+M) (`lhalf`, `rhalf`, `cat`, `Halves`),
  `diag-l`/`diag-r` (diag(a,d) acts by halves).
- `GluedSums`: `Diagonal[g,h].iso : P_{diag(g,h)} ~ P_g + P_h`.
- `Equaliser`: `Equalise` (psi localising at s, psi r = psi r' gives s^e r = s^e r'),
  `Combine`, and `Over.preimage`: unique r with ia r = u, ib r = v when ja u = jb v.
- `GluedFree`: `iso : A^M ~ P_1`.
- `StableSum`: the chain P_g+P_h ~ P_diag(g,h) ~ P_diag(gh,1) ~ P_gh+P_1 ~ P_gh+A^M.

## Status (2026-11-02, night): P_g finite projective (step 5) DONE, checked

`GluedProjective.Over.Projective[g,g',gi].theorem : FM.FiniteProjective P_g` (67 modules, 0.73 s;
same theory parameters, no new axioms): P_g is merely a retract of A^(M+M). Proof: StableSum
with h = g' gives P_g + P_g' ~ P_gg' + A^M; gg' = 1 so P_gg' ~ P_1 ~ A^M (Invariance with
beta = alpha = 1, then GluedFree); A^M + A^M ~ A^(M+M).
- `FreeModules`: `free K` (= A^K as SerreModuleProducts of `regular`), `Halving[M].iso`
  (A^(M+M) ~ A^M + A^M), `Retract[P]` / `FiniteProjective P` (the notion of
  chatelet/DescentProjective, for SerreModule), `Summand[P,Q,K,e].retract` (P + Q ~ A^K gives
  a retract).
- Instance: `Localisations.Over.Instance[..].ProjectiveAt[M].theorem`.

Next (see gabber-recollement.tex): a representation of K_0 (or of stable isomorphism classes
of f.g. projectives) so that Lemma 3.6(1) reads [P_g] + [P_h] = [P_gh] + M; Lemma 3.6(2)
needs tensor products P_g (x) P_h = P_{g (x) h} (no module tensor product in this directory
yet; check chatelet/exterior first); 3.6(3) needs bases of F + O^j on A_a, A_b.
Independent of this line: LQ X.5.5 (reduced K_0 is nil, for Lemma `roots`) and weak
cancellation (Lemma `efface`).

## K_0: the options (informal analysis, 2026-11-02)

What gabber-recollement uses: K = K_0 (x) Q, rho(F) = [F]/N; equations k([X] - [Y]) = 0,
i.e. X^k + T ~ Y^k + T; products (tensor) in `roots` (mu nilpotent, LQ X.5.5), `cheap`
(tensoring stable isos with V, W) and `correct` ((1 + tau)(1 - tau/n)^n = 1, tau^2 = 0 by
3.6(2)); restriction K_0(A) -> K_0(A_a) in 3.6(3) and `correct`.

- (A) No K_0: state every equation as a mere stable isomorphism of modules. Enough for
  3.6(1), 3.6(2) (module form, done), 3.6(3), weak cancellation, `cheap`. Not enough for
  `roots` and `correct`, which compute in a Q-algebra with nilpotents; unfolding those
  polynomial identities into module isomorphisms by hand is the wrong level.
- (B) K_0 from projectors: (e, k) with e an idempotent K x K matrix over A, meaning
  [im e] - k; equality = mere stable similarity; + = block sum, * = Kronecker (KRONECKER:
  mixed product, 1 (x) 1 = 1, so idempotents go to idempotents). Small (matrices over A), a set
  quotient (Quotient.seg), K_0 (x) Q by MonoidLocalization at positive integers, restriction
  by MatrixMap. Costs: ring laws up to similarity (permutation matrices for commutativity of
  (x) and of block sums), well-definedness on the quotient, and the bridge [P] = class of the
  projector of any retract of P (two retracts of one P give stably similar projectors).
  This is LQ's own setting, and lambda-operations for X.5.5 act on projectors.
- (C) K_0 from modules: iso classes of f.g. projective SerreModules (replacement for size),
  with a module tensor product. Unit has no module tensor product (sag/tensor and
  chatelet/Tensor are for algebras), so (C) costs a quotient construction with its laws
  up to iso before anything else.

Recommendation: (B), keeping the module statements (A) as the lemmas proved; they transfer
to (B) by "isomorphic modules have equal classes" and "+ is block sum".
The one place where (B) still needs real content is [P_g][P_h] = [P_{g (x) h}]: gluing
commutes with tensor products. Proof idea: a linear map of f.g. projective modules that is
an isomorphism after inverting a and after inverting b (a, b comaximal) is an isomorphism;
check it for im(e (x) f) -> P_{g (x) h} built from the retracts. The SerreModule
localisation files in ../qcqs (SerreModuleLocalisation*) may provide the local-global step.

## Status (2026-11-02, night): Lemma 3.6(2) at the module level DONE, checked

`GluedKronecker.Over[..,m,n].Lemma[g,g',gi,h,h',hi].theorem`: for inverse pairs g (n x n) and
h (m x m) over C, merely P_g^m + P_h^n ~ P_{h (x) g} + A^(times m n) (70 modules, 0.84 s; same
theory parameters, no new axioms). Instance: `Localisations...Instance[..].KroneckerAt[m,n]`.
- `Pairing`: `times`, `pair`/`unpair` (Fin (times m n) = Fin m * Fin n), sums as double sums,
  delta at pairs.
- `Kronecker`: `kron Y X` (entry Y_jj' X_ii'), `act-kron`, `mixed`, `kron-one`, `kron-inverse`.
- `GluedKronecker`: `Rows` (P_{1 (x) X} ~ P_X^m), `Columns` (P_{Y (x) 1} ~ P_Y^n), then
  STABLESUM for 1 (x) g and h (x) 1, with (1 (x) g)(h (x) 1) = h (x) g. No permutation matrix.
- `Glued.Equal[g,k,e]`: P_k ~ P_g for k = g (moved from GluedProjective).
Remaining for 3.6(2) proper: the K_0 product and [P_g][P_h] = [P_{g (x) h}] (see above).

## Status (2026-11-02, late night): K_0 (projector model) and the bridge DONE, checked

`K0.Over[A,setA].K0 : CRing` and `GluedTensor.Over[..,m,n].Bridge[g,g',gi,h,p,q,s,ep,eq,es].theorem`:
if p presents P_h, q presents P_g (g invertible) and s presents P_{h (x) g}, then
[p][q] = [s] in K_0(A) (81 modules, 2.14 s from a fresh server; heaviest declaration 0.14 s;
same theory parameters, no new axioms). Instance: `Localisations...Instance[..].BridgeAt[m,n]`.
Route (B) of the analysis above, with the tensor product given by "P (x) f" (Twist), so no
module tensor product and no rectangular matrices are needed.
- `DirectSums`: block sums dsum p q for sizes m, n (parts lpart/rpart/catv, act-l/act-r, dsum-mul).
- `Projectors`: `Projector` record (size, matrix, idempotent), `Image[p].image` (submodule of
  A^K), zeroP, oneP, `Sum[p,q]`, `Product[p,q]`.
- `ProjectorSums`: Image(dsum p q) ~ Image p + Image q; Image zeroP single.
- `ProjectorReindex`: `Reindex` (along an index bijection), `Swap`, `Assoc` for Kronecker.
- `Twist`: `Of[P,f]` = P (x) f = {c : Fin L -> P | sum f_yy' c_y' = c_y}; `Map` (functorial in P),
  `ImageOf` (Image(p (x) f) ~ Image p (x) f), `SumOf` (distributivity), `UnitOf`, `zero-single`.
- `ModuleIso`: + `Assoc`, `Swap`, `Single`, `Singles`, `ZeroRight`.
- `Semiring`: `CSemiring`, `FromCongruence` (quotient of a raw semiring by a congruence).
- `Grothendieck`: Grothendieck ring of a CSemiring (`ring`, `class`, `class-add`, `class-mul`,
  `effective`/`same-class`: same class iff a + u = b + u for some u).
- `K0`: the semiring of projectors up to isomorphic images, K_0 = its Grothendieck ring;
  `class`, `class-sum`, `class-product`, `class-iso`, `Presenting[P,p,q,e,f].same`.
- `GluedProjector`: for invertible g, merely a projector E (ia E = alpha D alpha',
  ib E = beta' D beta, D = blk 1 0 0 0) with Image E ~ P_g (`Explicit[g,g',gi].theorem`).
- `GluedTensor`: P_h (x) E ~ P_{h (x) g} (`Tensor`), and the bridge.
Also: `Vectors.mat-act`, `VectorBlocks.D/head/head-cat/head-head`, `VectorBlocks.Map`
(map-cat, map-D), `Kronecker.act-one-left/right`, `Pairing.Sums.swap-sums`, `Glued.Equal`.

Next: state Lemma 3.6(1) and 3.6(2) as K_0 equations, which needs [P_g^m] = m[P_g] (an
iso between the image of an m-fold block sum and the family product of SerreModuleProducts)
and the class of a free module; then 3.6(3) and the remaining items of gabber-recollement
(LQ X.5.5, weak cancellation, K_0 (x) Q by MonoidLocalization).

## Status (2026-11-02, after midnight): Lemma 3.6(1), 3.6(2) as K_0 equations DONE, checked

83 modules, 2.28 s from a fresh server (ClassSum 0.06 s, ClassProduct 0.02 s); same theory
parameters, no new axioms. Instances `Localisations...Instance[..].ClassSumAt[M]`, `ClassProductAt[m,n]`.
- `Projectors.Free[K]`: the unit projector 1_K, `iso : Image 1_K ~ A^K` (FreeModules.free K).
- `ProjectorSums.FreeSum[j,k].iso`: Image (1_j + 1_k) ~ Image 1_(j+k); `free-zero-single`.
- `K0`: `free K` (= [A^K]), `multiple j x`, `free-class` (a presenter of A^K has class free K),
  `class-zero`, `free-sum` ([A^j] + [A^k] = [A^(j+k)]), `free-zero`, `free-count` ([A^K] = K 1).
- `ClassSum.Over[..,M].Lemma[g,g',gi,h,h',hi,p,q,s,ep,eq,es].theorem`:
  [p] + [q] = [s] + [A^M] for p, q, s presenting P_g, P_h, P_gh (from STABLESUM).
  `ClassSum...Powers[g,g',gi,q,eq]`: `positive j` : [r] + j[A^M] = j[q] + [A^M] for r presenting
  P_(g^j), `negative j` : [r] + j[q] = (j+1)[A^M] for r presenting P_(g'^j) -- together the
  "[P_(g^j)] = j[P_g] - (j-1)M for j in Z" sentence. `power`/`copower`/`power-inverse` there.
- `ClassProduct.Over[..,m,n].Lemma[g,g',gi,h,h',hi,p,q,ep,eq].theorem`:
  ([p] - [A^m]) ([q] - [A^n]) = 0 for p presenting P_h (m x m), q presenting P_g (n x n).
  Proof uses only the bridge four times ([p][q], [A^m][q], [p][A^n], [A^m][A^n]) and ClassSum at
  N = mn for (1 (x) g)(h (x) 1) = h (x) g; no [P^m] = m[P] iso was needed. Presenters of the
  glued modules come merely from `GluedProjector.Explicit...theorem`. `Vanish` is the ring step.

Next: 3.6(3) and the remaining items of gabber-recollement (LQ X.5.5, weak cancellation,
K_0 (x) Q by MonoidLocalization).

## (Former brief) Lemma 3.6(1) at the module level

Goal: `[P_g] + [P_h] = [P_gh] + M` in K_0(A), for g, h in GL_M(A_ab), A_a, A_b, A_ab as in
`Localisations.Instance`. The matrix part is done: `Localisations.Over.Instance[..].DiagonalAt[M].theorem`
gives merely beta in GL_2M(A_b), alpha in GL_2M(A_a) with diag(g,h) = beta diag(gh,1) alpha.
What is missing is everything about modules:

1. **Glued module.** For g in GL_M(C) (C = A_ab, maps ja : A_a -> C, jb : A_b -> C),
   P_g = { (u, v) in A_a^M x A_b^M | jb(v) = g ja(u) } as an A-module (the A-action through
   A -> A_a and A -> A_b). This convention matches `Homotopy` (beta over A_b on the left, alpha
   over A_a on the right): jb(v) = beta g alpha ja(u) iff jb(beta' v) = g ja(alpha u), so
   (u, v) |-> (alpha u, beta' v) is an isomorphism P_{beta g alpha} -> P_g (beta' = beta^-1).
2. **Invariance** P_{beta g alpha} ≅ P_g (explicit A-linear iso, from inverse pairs).
3. **Sums** P_g ⊕ P_h ≅ P_{diag(g,h)} (uses `Blocks`: Fin(M+M) = Fin M + Fin M).
4. **P_1 ≅ A^M** (needs the sheaf property: A -> A_a x A_b -> A_ab is an equaliser for
   comaximal a, b; it may already exist in some form in sag/gluing (IdealGluing*, Localization*)
   or horrocks (LocalGlobal) -- search first).
5. **Finitely generated projective** P_g (needed for K_0): P_g is a direct summand of A^K.
   This is the real content (gluing of f.g. projectives); see LQ or the paper's "twisted modules".
6. **K_0**: decide representation. The statement only needs "stably isomorphic":
   P_g ⊕ P_h ≅ P_gh ⊕ A^M, which follows from 2-4 and avoids K_0 entirely. Recommended:
   prove that isomorphism and leave K_0 for later.

So the minimal target is: **P_g ⊕ P_h ≅ P_gh ⊕ A^M as A-modules** (steps 1-4 and 6; step 5 is
not needed for this isomorphism).

Existing pieces to check before writing (no module-level gluing exists yet in unit):
- `horrocks/LocalFree.seg`, `LocalGlobal.seg`: modules as quotients V/N with coordinates.
- `picard/`, `horrocks/`: projectors (idempotent matrices) for f.g. projective modules.
- `gluing/IdealGluing*.seg`, `gluing/Localization*.seg`: gluing for ideals / localisations.
- How A-modules and A-linear isomorphisms are represented elsewhere in sag (grep `Linear`,
  `Module`, `record Iso`) -- reuse one representation, do not invent a second.

Rules as above: every checker run < 60 s (`../segc sag/gluing-homotopy changed`), read
`../seg/WRITING.md`, lock constructions after their characterising lemmas, no ring solver,
`split` is a keyword (not a declaration name), and `module X = e` needs a module, not a value.
