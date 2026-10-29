# The doubled-origin line and the projective line

This note describes two examples for the locally ringed lattice
representation of schemes in `DESIGN.md`. Both glue two affine lines along
the punctured line. For the doubled-origin line the transition identifies
the coordinates; for the projective line it inverts them.

Work over a commutative ring `k`, allowing the zero ring. All descriptions
of `B`-points below are for commutative `k`-algebras `B` and morphisms over
`k`. Write `Zar(A)` for the Zariski lattice of a ring `A`, and `O_A` for
its structure sheaf on compact opens.

## Sections of extent u

An element of extent `u : Zar(B)` means a section `b : O_B(u)`.
If `u = D(a₁, …, aₙ)`, it can be represented by compatible elements

    bᵢ ∈ B[1/aᵢ],

whose restrictions agree in `B[1/(aᵢaⱼ)]`. The section itself does not
retain this choice of generators. Equality is equality of sections on the
same lattice element, independent of their presentations.

For a section `b : O_B(u)`, write `D_u(b) ≤ u` for its invertibility open.
Its defining property is

    w ≤ D_u(b)  iff  b restricted to w is invertible,    for w ≤ u.

This is the invertibility support of the locally ringed lattice.

## The doubled-origin line as a ringed lattice

Put `A = k[X]` and `d = D_A(X)`. Glue two copies of `Spec(A)` along
`Spec(k[X, X⁻¹])` using the identity transition on the coordinate.

The lattice of compact opens of the glued scheme is

    L = { (u₀, u₁) : Zar(A) × Zar(A) | u₀ ∧ d = u₁ ∧ d }.

The equality says that the two opens have the same restriction to the
identified punctured line. Bottom, top, meet and join are componentwise.
The defining equality is a proposition, so equality of lattice elements
reduces to equality of their two components.

The two chart opens are

    e₀ = (1, d),       e₁ = (d, 1).

They satisfy

    e₀ ∨ e₁ = 1,      e₀ ∧ e₁ = (d, d).

The principal ideals below `e₀` and `e₁` are each isomorphic to `Zar(A)`:
the first isomorphism sends `u` to `(u, u ∧ d)`, and the second sends `u`
to `(u ∧ d, u)`.

For `u = (u₀, u₁)` let `w = u₀ ∧ d = u₁ ∧ d`. Define

    O_L(u) = { (s₀, s₁) : O_A(u₀) × O_A(u₁)
                         | s₀ restricted to w = s₁ restricted to w }.

This is a pullback of rings. Restrictions and ring operations are
componentwise. The finite sheaf condition follows from the sheaf condition
on the two affine copies. The invertibility support is also componentwise:

    D_u(s₀, s₁) = (D_{u₀}(s₀), D_{u₁}(s₁)).

The components agree on the punctured line because `s₀` and `s₁` agree
there and invertibility support commutes with restriction.

Restricting this locally ringed lattice to either chart gives `Spec(A)`;
restricting to their intersection gives `Spec(k[X, X⁻¹])`. Thus this is a
qcqs scheme. The construction can be carried out directly using pairs and
the affine structure sheaf, before developing a general gluing theorem.

## Points of the doubled-origin line

A morphism from `Spec(B)` to the doubled-origin line determines the full
inverse images `u₀, u₁ : Zar(B)` of the two chart opens. Its two coordinate
sections agree on the intersection, so they glue uniquely to `t ∈ B`.
The resulting data satisfy

    u₀ ∨ u₁ = 1,      u₀ ∧ u₁ = D_B(t).

Conversely, these data determine a morphism: restrict `t` to each `uᵢ`
and use it as the coordinate map into the corresponding affine chart.
On the intersection `t` is invertible, so the maps glue through the
identified punctured line. The intersection equation ensures that `uᵢ`
are the full inverse images of the chart opens.

The intended classification is therefore

    Hom_k(Spec(B), doubled-origin line)
      ≃ { (t, u₀, u₁) | t : B, uᵢ : Zar(B),
                         u₀ ∨ u₁ = 1, u₀ ∧ u₁ = D_B(t) }.

These are properties of the data, not extra choices. Equality compares
`t`, `u₀` and `u₁`; no chosen finite presentations of the opens occur.

If `t` is a unit, both extents are top, giving a point of the common
punctured line. If `t = 0`, the extents form a complementary pair of opens,
describing the choice of origin on each part. In particular, over a field
there are two points with coordinate zero.

One can also begin with a chosen cover `v₀ ∨ v₁ = 1` and coordinate
sections agreeing and invertible on `v₀ ∧ v₁`. After gluing the coordinate
to `t`, these are merely smaller chart domains. The full inverse images
are obtained by saturation:

    u₀ = v₀ ∨ D_B(t),      u₁ = v₁ ∨ D_B(t).

Since `v₀ ∧ v₁ ≤ D_B(t)`, distributivity gives
`u₀ ∧ u₁ = D_B(t)`. Saturation removes the redundant cover choices.

## Thierry's description by an idempotent modulo t

Thierry's further observation turns the pair of extents into a single
algebraic datum. Fix `t : B`, put `d = D_B(t)`, and let `q : B → B/(t)`
be the quotient map. There is a canonical lattice isomorphism

    Zar(B/(t)) ≅ { u : Zar(B) | d ≤ u }.

The lattice on the right has bottom `d`, top `1`, and the inherited meet
and join. For a finite family `a`, the class `D(q(a))` corresponds to
`d ∨ D(a)`. This expresses restriction to the closed subscheme `t = 0`:
adding its open complement `D(t)` makes the lift of an open unique.

Consequently, the equations

    u₀ ∨ u₁ = 1,      u₀ ∧ u₁ = d

say exactly that the corresponding opens of `Zar(B/(t))` are complements.
Complementary opens of the Zariski lattice of a ring `C` correspond to
idempotents of `C`: an idempotent `e` gives the ordered pair

    (D_C(e), D_C(1-e)).

Conversely, the sheaf property glues the values `1` on the first open and
`0` on its complement to a unique global idempotent. Thus the correspondence
is constructive and does not require choosing prime ideals.

Define

    Idem(C) = { e : C | e² = e }.

The point classification becomes

    Hom_k(Spec(B), doubled-origin line) ≃ Σ (t : B), Idem(B/(t)).

This equivalence should be proved natural in `B`. A ring map `B → C`
sends `t` to its image and induces `B/(t) → C/(image(t))`, carrying the
idempotent along with it.

Explicitly, if `e : Idem(B/(t))` has a representative `a : B`, the extents
are

    u₀ = D_B(t) ∨ D_B(a),
    u₁ = D_B(t) ∨ D_B(1-a).

Their join is top. Their meet is `D_B(t)`, since `a(1-a)` belongs to `(t)`.
These extents are independent of the representative `a`: changing it by
a multiple of `t` does not change either join with `D_B(t)`. Representatives
can therefore be used under truncation to construct the unique pair of
extents; no global choice of representatives is required.

With this convention, `e = 1` selects the first origin and `e = 0` selects
the second. Exchanging the chart labels replaces `e` by `1-e`.

This gives a smaller candidate interface for points than retaining both
extents. Its implementation requires two reusable results: the quotient
lattice isomorphism above, and the equivalence between idempotents and
complementary opens. The lattice-and-sheaf construction still supplies the
scheme itself.

## The internal description

The accompanying internal description, reported by Thierry following an
observation of Felix, is

    S = Σ (r : R), ((r = 0) → 2),

where `R` is the generic ring, `2` is the two-element type, and `r = 0`
is the equality proposition. It is a function type on that proposition,
not a decision procedure for whether `r` vanishes.

The projection `S → R` is the fold map. If `r` is invertible, `r = 0` is
empty in the usual nontrivial local-ring setting, so there is a unique
function from it to `2`. At `r = 0`, the equality proposition is
contractible, and its function type into `2` is equivalent to `2`.
Thus the formula gives one point over the invertible locus and two over
zero, without deciding whether an arbitrary `r` is zero.

To relate this to algebra, work in the synthetic setting where functions
`Sp(A) → 2` correspond to idempotents of finitely presented algebras `A`.
For `r : A`, the zero locus inside `Sp(A)` is

    { x : Sp(A) | x(r) = 0 } ≃ Sp(A/(r)).

It follows, under that synthetic correspondence, that functions from this
zero locus to `2` correspond to `Idem(A/(r))`. This recovers the algebraic
classification of points above. Here the equality proposition at a generic
element and the zero locus of an element of an algebra are related by
evaluation; they should not be conflated in a formal statement.

The external functor `B ↦ Σ(t : B), Idem(B/(t))` and the locally ringed
lattice construction make sense over arbitrary commutative rings without
Loc, SQC or Z-choice. Comparing them to the internal formula is a separate
synthetic theorem, with its hypotheses stated explicitly. It need not be
a dependency of the qcqs construction.

## Global sections and the two origins

Global sections are pairs of polynomials agreeing after inverting `X`:

    Γ(L) = k[X] ×_{k[X, X⁻¹]} k[X] ≅ k[X].

The localisation map is injective because multiplication by `X` is
injective on `k[X]`, over any commutative base ring. Thus the two
polynomials in such a pair are equal.

The canonical map to `Spec(Γ(L))` is the map folding the two copies of the
line together. The lattice distinguishes their origins even though the
global section ring does not. Over a field the two origins are distinct,
so this example is not affine. It also shows why affine chart overlaps
do not imply separatedness: its overlap is affine, but its diagonal is
not closed.

## Comparison with the projective line

For `P¹_k`, glue `Spec(k[X])` and `Spec(k[Y])` along their punctured lines
using `Y = X⁻¹`. Its lattice has the same pair construction, with the
overlap equality transported through this coordinate inversion. Its
sections are pairs agreeing under the corresponding Laurent-ring
isomorphism.

A morphism `Spec(B) → P¹_k` is described by full chart inverse images
`u₀, u₁ : Zar(B)` and sections

    b₀ : O_B(u₀),       b₁ : O_B(u₁),

with

    u₀ ∨ u₁ = 1,
    u₀ ∧ u₁ = D_{u₀}(b₀) = D_{u₁}(b₁),
    (b₀ restricted to u₀ ∧ u₁) · (b₁ restricted to u₀ ∧ u₁) = 1.

Here `D_{uᵢ}(bᵢ)` is viewed as an element of `Zar(B)` below `uᵢ`.
The invertibility-open equations express that the extents are the full
inverse images of the standard charts.

The product equation alone suffices to glue maps on a chosen cover, but
does not give a unique representation of the resulting morphism. For
example,

    u₀ = 1, u₁ = 0, b₀ = 1

and

    u₀ = u₁ = 1, b₀ = b₁ = 1

describe the same morphism. The section on the empty open is unique.
Using full chart inverse images removes this redundancy. Starting with
an arbitrary such cover, their extents are

    u₀' = u₀ ∨ D_{u₁}(b₁),
    u₁' = u₁ ∨ D_{u₀}(b₀),

and the sections extend by the reciprocal transition.

## Rank-one direct summands for P¹

The same data describe a rank-one direct-summand submodule of `B²`.
On the first chart it is generated by `(b₀, 1)`; on the second it is
generated by `(1, b₁)`. On their intersection,

    (b₀, 1) = b₀ · (1, b₁),

with `b₀` invertible, so the generated submodules agree. Written on finite
principal-open presentations of `u₀` and `u₁`, these are precisely the
compatible local generators in the motivating discussion.

Conversely, a rank-one locally free direct-summand submodule of `B²`
has two coordinate loci: where its second coordinate projection is an
isomorphism, and where its first coordinate projection is an isomorphism.
They cover `Spec(B)`. Normalising the respective coordinates to one gives
`(b₀, 1)` and `(1, b₁)`, with the reciprocal transition above.

This gives a later comparison theorem between the geometric construction
of `P¹` and rank-one direct summands. The module description need not be
part of the definition of `P¹`.

## Suggested implementation order

1. Finish the affine structure sheaf and its invertibility support.
2. Construct the doubled-origin lattice and sheaf directly as compatible
   pairs; identify its two affine charts and their overlap.
3. Prove the classification of its `B`-points, including saturation of
   arbitrary chart covers.
4. Prove `Zar(B/(t)) ≅ [D_B(t), 1]` and the correspondence between
   complementary opens and idempotents; deduce the natural classification
   `Σ(t : B), Idem(B/(t))`.
5. Compute its global sections and exhibit the fold map.
6. Repeat the pair construction with reciprocal transition for `P¹`.
7. Prove the comparison with rank-one direct summands when the required
   module descent interface is available.
8. Separately, compare with the internal formula in the synthetic setting.

These are proposed constructions and theorem statements. They are not
yet checked Unit declarations.
