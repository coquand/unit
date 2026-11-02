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

## Next: Lemma 3.6(1) at the module level (new infrastructure; start here in a fresh session)

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
