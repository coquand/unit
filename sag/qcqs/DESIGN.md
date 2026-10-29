# qcqs schemes as locally ringed lattices

Sources (in `~/CANONICITY/SCHEME`):

- `zeuner1.pdf` — Zeuner, *Univalent foundations of constructive algebraic
  geometry*: qcqs schemes as locally ringed lattices, Spec ⊣ Γ (Thm 3.12),
  comparison with functorial schemes. **The spine of this development.**
- `zeuner2.pdf` — Zeuner–Mörtberg, affine schemes via the Zariski lattice.
- `zeuner3.pdf` — Zeuner–Hutzler, functorial qcqs schemes (later, step 6).
- `isaev.pdf` — scheme sites; we take its abstract treatment of localisation
  (Def. 2.1, Lemmas 2.2–2.5), not its notion of morphism.

## Principles

1. **Universal properties, universal-algebra style.** Each object is given
   with the statement "for every T and g with property P there is a unique h
   with h ∘ f = g", for that specific object. No category library at the
   start; categories, functors and adjunctions come at the end (step 6).
2. **No ring solver.** Ring identities are proved as a mathematician writes
   them, through a few named lemmas (as in `sag/exterior`).
3. **Constructions are used once.** A construction (fractions, lists modulo
   radical) proves the universal property and is then locked; later files use
   only the property.
4. Files follow `~/CANONICITY/seg/WRITING.md` (informal proof first in the
   file comment, one name per notion, "by definition" facts as refl lemmas,
   lock after characterising lemmas, check `--opened`); checks through
   `segc`, each file under 1 s.

## Step 1 — Localisation as a property

`IsLoc S f` for `f : R → T` a ring map and `S` a multiplicative monoid of `R`:
`f` inverts `S`, and for every ring map `g : R → T'` inverting `S` the type
of extensions `(h : T → T') × (h ∘ f = g)` is contractible.
Elementary form (Isaev Def. 2.1), with truncated existence: `f` inverts
`S`; every `z : T` merely has `y ∈ A`, `s ∈ S` with `f(s) z = f(y)`; `f(y) = 0`
implies merely `ys = 0` for some `s ∈ S`. The two forms are proved
equivalent early (the direction from the universal property compares with
the fractions), so later arguments use whichever is convenient.

- Existence: the fraction construction. Reuse `sag/pn/MonoidLocalization`
  (arbitrary monoid, representatives, kernel detection) and
  `sag/pn/MonoidLocalizationMap` (induced homomorphism), packaged with
  uniqueness into the abstract interface, rather than adding a fifth copy;
  the other copies (`sag/affine/Localization`, `sag/chatelet/Localization`,
  `sag/cffr/Localisation`) are left alone. These files use funext,
  univalence and quotients only, not Loc, SQC or Z-choice.
- Isaev Lemmas 2.2 (composition), 2.3 (cancellation), 2.4 (`R_x = R_y` iff
  `x | yⁿ` and `y | xᵏ`), 2.5 (unit ideal), from the property only.
- Notation: `R_g` = localisation at the powers of `g`.

## Step 2 — The Zariski lattice as the universal support

A *support* `d : R → L` into a distributive lattice: `d 1 = ⊤`, `d 0 = ⊥`,
`d (ab) = d a ∧ d b`, `d (a + b) ≤ d a ∨ d b`.

- `D : R → L_R` is the universal support: every support `d : R → L` factors
  uniquely through a lattice map `L_R → L`.
- Construction: finite lists of elements of `R` modulo
  `(a₁..aₙ) ≤ (b₁..bₘ)` iff each `aᵢ` has a power in the ideal `(b₁..bₘ)`;
  a set quotient, at the level of `R`.
- **Milestone:** the formal Nullstellensatz,
  `D(a₁..aₙ) ≤ D(b₁..bₘ)` iff every `aᵢ` has a power in `(b₁..bₘ)`.
- Useful identities: `D g ∧ D(f₁..fₙ) = D(g f₁..g fₙ)`;
  `D(f₁..fₙ) = ⊤` iff `(f₁..fₙ) = (1)`.
- **Bridge** (connects steps 1 and 2): `D h ≤ D g` iff `g` becomes
  invertible in `R_h`. Hence `ρ_{h,g} : R_g → R_h` for `D h ≤ D g` by the
  universal property, with `ρ_{g,g} = id` and `ρ_{k,h} ∘ ρ_{h,g} = ρ_{k,g}`
  by uniqueness.

## Step 3 — The structure sheaf on all of L_R

For `U : L_R`, indexed by ring elements, not by basic opens:

    O(U) = { s ∈ Π (g : R) (D g ≤ U), R_g  |  s_h = ρ_{h,g}(s_g) whenever D h ≤ D g }

- Restriction for `U ≤ V` forgets components. Only the component formula
  holds by `refl`; identity and composition need section extensionality
  and component proof independence (the witnesses of `≤` differ).
- No presentation of `U` is involved, so no independence-of-presentation
  argument, and no use of univalence beyond the quotient already behind
  `L_R`: the ring-valued family is never descended through that quotient.
  Equal basic opens `D g = D g'` are related by the canonical mutually
  inverse maps `ρ`; their carriers are never identified.
- `O(D f) ≅ R_f`: component at `f`, inverse `x ↦ (ρ_{g,f} x)_g`.
- Universal property: a ring map `T → O(U)` is a compatible family of ring
  maps `T → R_g` (limit of rings).
- **Basic sheaf lemma** (the only place a cover is used): if
  `1 = Σ aᵢ fᵢ` in `R_g`, then
  `R_g → Π R_{g fᵢ} ⇉ Π R_{g fᵢ fⱼ}` is an equaliser.
- **Sheaf property on `L_R`:** for `U = U₁ ∨ … ∨ Uₙ`, `O(U)` is the equaliser
  of `Π O(Uᵢ) ⇉ Π O(Uᵢ ∧ Uⱼ)`; reduced to the basic lemma via
  `D g ∧ D(f₁..fₙ) = D(g f₁..g fₙ)`.
- **Extension lemma for maps out of `O`** (the useful part of the
  comparison lemma, without a category library): given a sheaf `G` on a
  lattice `M`, a lattice map `π : L_R → M` and ring maps
  `φ_g : R_g → G(π(D g))` compatible with restriction, for every `U` and
  `s ∈ O(U)` there is a unique `t ∈ G(π U)` with `t|π(D g) = φ_g(s_g)` for
  all `D g ≤ U`. The statement is a proposition, so a merely existing
  finite presentation of `U` can be used (gluing in `G`); the map
  `O(U) → G(π U)` is read off from the unique `t`, hence independent of the
  presentation. The limit property only gives maps into `O(U)`; step 5
  needs this one.
- Same construction for an `R`-module `M` with `M_g` in place of `R_g`.

## Step 4 — Locally ringed lattices

- A ringed lattice: distributive lattice `L` with a sheaf of rings `O` on
  finite covers (stated concretely: families of rings and restriction maps
  with the finite equaliser condition).
- Locality is zeuner1 Def. 3.2–3.4. An *invertibility supremum* of
  `s ∈ O(u)` is `u_s ≤ u` with, for all `w ≤ u`,
  `w ≤ u_s ⇔ s|w is invertible`. It is unique (Remark 3.3), so an
  invertibility map `D_u : O(u) → ↓u` is a property of `(L, O)`, not extra
  structure. A locally ringed lattice is a ringed lattice with an
  invertibility map such that each `D_u` is a support. Merely giving a
  support on every section ring is not enough.
- Derived: compatibility of `D` with restriction.
- Morphisms: `π* D_u(s) = D_{π* u}(π♯ s)`; `≤` always holds (Remark 3.6),
  so only `≥` is required.
- `Spec R = (L_R, O)` is a locally ringed lattice. On an arbitrary `U` the
  invertibility open needs a finite presentation of `U`: eliminate into the
  proposition "there is a unique invertibility supremum".

Order of work (review of 2026-10-29), three stages kept distinct:

1. **Abstract invertibility opens**, over any `RingedLattice` sheaf:
   `IsInvOpen u s v` iff `v ≤ u` and, for all `w ≤ u`,
   `w ≤ v ⇔ s|w is invertible`. Prove uniqueness and compatibility with
   restriction *before* imposing any support laws.
2. **Invertibility support on Spec A.** On a basic open `D g`, a fraction
   `a/gⁿ` has invertibility open `D(ga)`: prove this characterisation first;
   uniqueness of invertibility opens makes it independent of the fraction
   chosen. For an arbitrary `u`, take a finite presentation and join the
   local invertibility opens, eliminating the presentation into unique
   existence (as in `Sheaf` and `Extension`).
3. **Locally ringed lattices and their morphisms.** Require the support laws
   on the invertibility map; define morphisms by preservation of the
   invertibility support. Then package the affine construction as `Spec A`.

The doubled-origin line follows directly: its invertibility support is
componentwise, and agreement on the overlap follows from compatibility with
restriction.

## Step 5 — Γ ⊣ Spec, affine and qcqs schemes

- The concrete correspondence is primary (it avoids the conventions: in
  zeuner1, Def. 3.10–3.11 and Thm 3.12 work in `LRDL^op` and
  `CommRing^op`, where Spec is right adjoint to Γ): geometric morphisms
  `X → Spec R` correspond one-to-one with ring maps `R → O_X(⊤)`. The map
  `φ : R → O_X(⊤)` determines the lattice map `L_R → L_X` by step 2's
  universal property (`r ↦ D_⊤(φ r)`), and the sheaf map by step 3's
  extension lemma.
- Affine is a property: the canonical map `X → Spec Γ(X)` (the
  correspondence at the identity of `Γ(X)`) is an isomorphism.
- qcqs scheme is a property: there merely exist `u₁, …, uₙ` with
  `⊤ = u₁ ∨ … ∨ uₙ` and each `X|uᵢ` affine. Actual cover data is a parameter
  of separate modules used in proofs. Overlaps are not required to be
  affine (requiring it would restrict the class: it is semi-separatedness,
  not separatedness — the doubled-origin line has affine overlaps); quasi-separatedness is
  automatic, since `uᵢ ∧ uⱼ` is again a compact open with a finite affine
  cover.
- zeuner1 Prop. 3.20 and Cor. 3.21: `O_X(D_u s) ≅ O_X(u)[1/s]` for **every**
  `u` of a qcqs scheme, not only affine `u`.

## Step 6 — Later

- A minimal category layer; Γ ⊣ Spec as an adjunction; univalence of the
  category of locally ringed lattices (zeuner1 Prop. 3.7).
- Functor of points and the comparison with functorial qcqs schemes
  (zeuner1 §4–5, zeuner3). Size: functors on `CommRing_ℓ` live one level up.

## Independence

This development does not use Loc, SQC or Z-choice: it is about schemes
over an arbitrary commutative ring. The synthetic directories provide
algebraic infrastructure only.

## Status

Latest checkpoint (2026-10-29): 249 modules, zero failures. Both absolute
and relative totalisation, essential image, and equivalence of univalent
categories are checked. RelativeTotalisation proves the intrinsic native
sheaf and qcqs criteria for the total functor. RelativeEssentialImage
proves relative representability, and RelativeCategories.equivalence
packages the comparison over an arbitrary base ring with an inverse
functor and both natural isomorphisms. The independent full audit checks
9,250 declarations with no extra openings in all 3,752 lists. The final
relative checkpoint below records the proof, implementation and validation;
the earlier checkpoints retain their historical continuation boundaries.


Checked (`../../segc qcqs all`: 74 modules, 0 failed, about 1.4 s):

- `RingMaps`: named parts of a ring map (`map`, `map-one`, `map-add`, `map-mul`,
  `map-zero`, `map-neg`; `map-identity`, `map-compose` by definition).
- `Localisation`: `IsLoc` (inversion + contractible extensions), the
  elementary form, and **elementary ⇒ universal** (values along fractions,
  transfer, fraction rules; `universal` locked after `is-loc`);
  `inverts-after` and `Agree`: two maps out of a localisation that agree
  on `A` are equal.
- `LocalisationFractions`: the fractions `A[S⁻¹]` are a localisation;
  **universal ⇒ elementary** (comparison with the fractions).
- `Radical`: ideals and radicals of finite families; the two-powers lemma
  `(u+v)^(p+q) = X u^p + Y v^q` (no binomial theorem); the radical is an
  ideal; the order `a ≤ b` on families is a preorder.
- `DistLattice`: bounded distributive lattices as algebras, the order
  `x ≤ y ⇔ x ∧ y = x`, finite joins, lattice maps with named parts
  (`hmap`, `hmap-bot`, …), `preserves` (maps preserve finite joins),
  `meet-joins` (distributivity over finite joins), supports
  (`d x ≤ d(xᵏ)`, `d(Σ vᵢbᵢ) ≤ ⋁ d(bᵢ)`).
- `FamilyLattice`: `++`, `*`, `(1)`, `()` on families with their order
  facts (lub, glb, top, bottom, distributivity).
- `ZariskiLattice`: `L_A` as the quotient, the lattice laws, `D` a support,
  the **formal Nullstellensatz** `[a] ≤ [b] ⇔ a ≤ b` (`order`, `reflect`),
  and **finite generation** `[a] = ⋁ᵢ D(aᵢ)` (`generated`). Public
  interface: `lattice` (carrier `lattice.L`, operations `lattice.join`,
  …), `cls`, `join-cls`, `meet-cls`, `bot-cls`, `top-cls`, `forall1-3`,
  `D`, `support`, `order`, `reflect`, `generated`; the descended
  operations are locked after `join-cls`/`meet-cls`.
  Presentations (step 3, item 1), the only access to opens later files
  need: `Presentation u` (`generators`, `presents`: `u = ⋁ D(a_j)`),
  `presented : ∥Presentation u∥`, `gen-below`, `bot-presentation`,
  `join-presents`/`join-presentation`; `Refinement n us`: a presentation
  of `⋁ u_i` whose generators each lie below one `u_i` (`count`, `piece`,
  `refines`, `tag`, `tag-below`), `refined : ∥Refinement n us∥` by finite
  choice; `BasicCover[g,n,a,le]` for `D g ≤ ⋁ D(a_j)`: `below`,
  `below-gen`, `covers`, `join-eq : D g = ⋁ D(g a_j)`. `D` is typed
  `lattice.L`, so clients never compare through the quotient.
- `ZariskiUniversal`: **D is the universal support**: for a support
  `d : A → M`, `factor : Hom L_A M` with `factor-D : factor(D x) = d x`,
  and `unique`: every lattice map `k` with `k(D x) = d x` agrees with
  `factor` (pointwise; via `generated`). `factor-cls : factor[a] = ⋁ d(aᵢ)`.
  The quotient is not used after this file.
- `Bridge` (over `A`, `h`): the powers of `h` as a monoid (`Powers`,
  `LocH` = localisation at them); `Below g = ∥hⁿ = g y∥ ⇔ D h ≤ D g`
  (`below-le`, `le-below`); for an elementary localisation `f` at the
  powers of `h` into a set, `f(g)` invertible ⇔ `D h ≤ D g`
  (`At.invertible-le`, `At.le-invertible`).
- `Restriction` (over a family `f_g : A → R_g` of elementary
  localisations at the powers of `g`, each `R_g` a set): `Pair[g,h,le].rho
  : R_g → R_h` for `D h ≤ D g` with `rho-on : ρ(f_g a) = f_h a`;
  `rho-id : ρ_{g,g} = id`, `rho-comp : ρ_{k,h} ∘ ρ_{h,g} = ρ_{k,g}`.

- `Sections` (step 3, over the family of `Restriction`): `rho`, `rho-irr`
  (independent of the witness), `rho-on`/`rho-id-at`/`rho-comp-at` on
  elements; `Section u` = compatible families `s_g`, `D g <= u` (accessors
  `at`, `compat`), `component-irr`, `section-ext` (sections with equal
  components are equal), `section-set`; `restrict` with `restrict-at` by
  refl, `restrict-id`, `restrict-comp`; the ring `ring u` (componentwise,
  `Ops[u].add-at`/`mul-at` by refl); `restriction` and `component` (π_g)
  are ring maps.
- `BasicOpen`: `O(D g) ≅ R_g`: `evaluation = component at g`, inverse
  `extend x = (rho_{g,h} x)_h`, `iso` (no cover, no presentation);
  `natural`: `eval_h(s|D h) = ρ_{g,h}(eval_g s)`.
- `Limit`: O(u) is the limit of the R_g: cones (`Maps`, `Cone`), the
  components of a ring map form one; `Lift.lift` with `lift-proj` by refl
  and `unique` (pointwise, as in `ZariskiUniversal`).
- `Separation` (`Cover[g,n,hs,below,covers]`, `D g = ⋁ D h_i`): `separated`
  (ρ_i x = 0 for all i ⇒ x = 0), `injective`; `refines`/`radical-of`
  (`D h_i ≤ D t_i` ⇒ g in the radical of (t)); `image-num` (the image of a
  fraction under ρ); `Single[h,k,..].injective` for `D h = D k`.
- `NatBound`: `bound` (sum) of finitely many naturals, `bound-above`,
  `above-trans` — one exponent for finitely many killers.
- `Gluing` (`Cover[g,n,hs,below,covers,xs,agree]`, agreement in
  `R_{h_i h_j}`): **the basic sheaf lemma** `sheaf : isContr Glue`, Glue =
  `(x : R_g) × (ρ_i x = x_i)`. Normal form (`Fr`, `Ks`: `k_i = h_i^(M+1) s_i`
  with exact cross relations), strict case (`Strict.Rad`: `x = f(Σ y_i c_i)
  / f(g^p)`), back to the `h_i` by `Single.injective`.
- `Separated`: `Pair[u,u2,s,s2].Agree v` (s ∈ O(u), s2 ∈ O(u2) have equal
  components below v; `agree-prop`); `Local` (agreement on the generators
  of a presentation, by `Separation`), `Join` (binary, through
  presentations), `agree-bot`, `agree-joins`, `agree-cover`,
  `agree-restrict`; `equal`; `Cover[u,n,us,le,covers]`: `separated`,
  `Amalgam xs` (`amalgam`, `matches`), `amalgam-prop`.
- `Sheaf` (`Cover[u,n,us,le,covers,xs,compatible]`, compatibility as
  equality of restrictions to `u_i ∧ u_j`): **the sheaf property on L_A**
  `sheaf : isContr Amalgam`, for every finite cover of every open (the empty
  cover included). Built one component at a time: `Glued g` (y ∈ O(D g)
  agreeing with each x_i on `D g ∧ u_i`) is a proposition (`glued-prop`);
  `Basic.Refined` glues over a refinement with `Gluing.sheaf`;
  `component g = eval(y_g)`, compatible by `natural` and `glued-prop`. `structure`/`structure-sheaf`: O as an instance of `RingedLattice`.
- `RingedLattice` (`On[M]`): the concrete interface for sheaves of rings on a
  distributive lattice: record `Presheaf` (`ring`, `ring-set`, `res`,
  `res-id`, `res-comp`); `Of[G]`: `restrict`, `res-irr`, `Cover[..]` with
  `Compatible`, `Matches`, `Amalgam`, `restrictions(-compatible)`, and
  `IsSheaf` (every finite cover, the empty one included);
  `Sheaf[G,sheaf].Cover`: `glue`, `separated`. Also in `DistLattice`:
  `le-of-eq`, `JoinMaps.monotone`.
- `Extension` (`Over[..,M,G,sheafG,pi].Extend[phi,phi-compat]`): **the
  extension lemma**. `Fits u s t` (`t|π(D g) = φ_g(s_g)` for all `D g ≤ u`),
  `Ext u s` a proposition (`ext-prop`, separation in G along a merely given
  presentation); `Exists` from a presentation (`compatible` via
  `π(D a_j) ∧ π(D a_k) ≤ π(D(a_j a_k))`, `At.fits-g` by separation over
  the `π(D(g a_j))`); `extend`, `extend-fits`, `unique`; then by uniqueness:
  `extension-map` (a ring map), `extend-restrict`, `extend-basic`
  (`= φ_g ∘ eval` on `D g`), `Unique.agrees` (the only such family).

- `InvOpen` (step 4, stage 1; `On[M].Of[G]`, any presheaf of rings):
  `Unit`, `IsInvOpen u s v` (`below`, `to-unit`, `from-unit`; clauses
  `Forward`/`Backward`), a proposition; `unit-on`, **`unique`** (Remark
  3.3), `InvOpen`/`inv-open-prop`, `InvMap`/`inv-map-prop`;
  `Restrict.restrict` (`w ∧ v` is the open of `s|w`) and `restrict-eq`;
  `whole` (a unit is invertible everywhere); `res-twice`, `unit-twice`,
  `unit-once`, `unit-restrict`. In a sheaf (`Local[sheaf]`): `Units` (units
  are local), `Basis[B,el].Criterion` (test on a basis), `Join`
  (`D_{⋁uᵢ}(s) = ⋁ D_{uᵢ}(s|uᵢ)`). No support law used. Also
  `DistLattice.Joins.meet-cover`.
- `SpecInv` (stage 2): `Units[h]` (units of O(D h) = units of R_h via
  evaluation), `Fraction` (for `x = a/gⁿ`, `D h ≤ D g`: `ρ(x)` unit ⇔
  `D h ≤ D(ga)`), `basis`, `Basic[g,s]` (`D(ga)` is the open; `on-fraction`:
  independent of the fraction), `General[u,s]` (presentation + `Join`),
  `inv-map`, locked after its definition.
- `LocallyRinged` (stage 3): `Laws[G,inv]`: `d`, `d-open`; **`one-law` and
  `mul-law` hold for every invertibility map**, so the conditions are
  `ZeroLaw` and `AddLaw`; `IsSupport` (Def. 3.4), `support`; record
  `LocallyRinged` (`sheaf`, `is-sheaf`, `inv`, `is-support`), which
  packages varying sheaf data; over a fixed ringed lattice, locality (an
  invertibility map that is a support) is a proposition. `Maps[L,M,F,G]`: record `Ringed` (`lat`, `sharp`,
  `natural`); `Of[pi,DF,DG]`: `image-le` (Remark 3.6, `π D_u s ≤
  D_{πu}(π♯ s)`), `IsLocal` (the converse), `local-eq`.
- `SpecLocal` (stage 3): `Test` (an inequality tested on basic opens),
  `zero-law` (Bridge at 0), `add-law` (fractions `a/p`, `c/q` on `D b`:
  `f(qa+pc) = f(p)f(q)(x+y)`), and **`spec : LocallyRinged`** on `L_A`.

Step 4 stages 1–3 are done (2026-10-29).

- `FibreProduct` (`Over[A,B,C,sets,f,g]`): the ring `A ×_C B` of pairs
  with `f a = g b` (`pair`, `left`, `right`, `agree`, `ext`, `pair-set`,
  `proj-left`/`proj-right` ring maps by definition); **universal
  property** `Lift[T,p,q,e].lift` with `left-lift`/`right-lift` by refl and
  `unique`; `(a, b)` is a unit iff `a` and `b` are (`unit-left`,
  `unit-right`, `unit-pair`). Also `DistLattice.Joins.meet-join-right`.
- `DoubleLattice` (`Over[L,d]`): `L₂ = {(u,v) | u ∧ d = v ∧ d}` (`Opens`,
  `pair`, `first`, `second`, `overlap`, `ext`), the lattice `lattice`
  componentwise; projections `first-map`/`second-map` are lattice maps, so
  `le-first`/`le-second`/`join-first`/`join-second` come from `JoinMaps`;
  `le-pair`; `mid x = first x ∧ d` with `mid-first`, `mid-second`,
  `mid-le`; `restrict-d` (`x ≤ u ⇒ (u ∧ d) ∧ x = x ∧ d`).
- `Doubling` (`Over[L,X,d]`, X any `LocallyRinged`): **the doubling of a
  locally ringed lattice along an open**. Sections over `x` are
  `O(first x) ×_{O(mid x)} O(second x)` (`At[x].P`, accessors `left`,
  `right`, `agree`, `ext`); `Res` by `Lift` (`left-res`/`right-res` by
  refl); `presheaf`; `Glue` (amalgams componentwise, agreement on `mid` by
  separation on the cover `mid (ms i)`, uniqueness by separation) gives
  `is-sheaf`; `Inv` (`D₂(s,t) = (D s, D t)`, in `L₂` by `InvOpen.Restrict`
  + uniqueness; units of a fibre product) gives `inv`; `d-first`/
  `d-second` by refl; `zero-law`, `add-law`; **`doubled : LR2.LocallyRinged`**.
- `Chart` (`Over[L,X,d]`): **each chart of the doubling is X**. First chart
  `e = (⊤, d)`, `iota u = (u, u ∧ d)`: `iota-join`, `iota-meet`, `iota-le`,
  `iota-below`, `iota-first` (every `x ≤ e` is `iota (first x)`);
  `to u : O(u) → O₂(iota u)`, `s ↦ (s, s|(u ∧ d))` by `Lift`, inverse the
  first component (`left-to` by refl, `to-left`); `natural`; `inv-to`:
  `D₂(to s) = iota(D_u s)` (via `inv-second`). Second chart `e2 = (d, ⊤)`,
  `iota2 u = (u ∧ d, u)`, `to2`, `natural2`, `inv-to2`; there
  `mid (iota2 u) = (u ∧ d) ∧ d` is not `u ∧ d` by definition, so
  `At2.to-right` restricts through it.
- `Affine` (`Over[A]`, any ring): the localisation family fixed to the
  fractions `A[1/g]` (`Loc`, `set`, `inclusion`, `elementary` from
  `LocalisationFractions`); **`spec`**. The only place the family is fixed.
- `DoubledLine` (`Over[k,setk]`): `line = Spec k[X]`, `punctured = D(X)`,
  **`doubled-line`**, and `Charts` (both charts are `line`).

Next 1–3 are done (2026-10-29): the doubling of any locally ringed lattice
along an open, the doubled-origin line over any ring `k`, and its two
charts, as concrete isomorphisms (lattice part, ring part natural in `u`,
invertibility opens preserved), not through a slice construction.

- `Global` (step 5, item 1; `Over[A,setA,..]`, A a set): **Γ(Spec A) = A**.
  `Of[u].section a` = `a|u` (components `f_g(a)`, `section-at` by refl),
  `sections` a ring map; `back : R_1 → A` from the universal property (the
  identity inverts the powers of 1), `back-f`, `f-back` (Agree); `global`,
  `evaluate`, `iso`. `top-D : top = D 1` by refl, `below-one` moves a
  witness along it once.
- `SpecMap` (item 2; `Over[..,M,X,phi]`, `phi : A → O_X(⊤)`): the support
  `d r = D_⊤(φ r)` (`d-support`; one/mul laws from `LocallyRinged`, zero/add
  from `X.is-support`), `pi = factor`, `pi-D`; `Basic[g].phi-g : R_g →
  O_X(π(D g))` by the universal property (`inverts`: `π(D g) = d g ≤ d(gⁿ)`),
  `phi-g-on`; `Compat`/`phi-compat` by Agree; `E = Extension…Extend`,
  `natural`, **`morphism`**; `LocalBasic` (`y t = (φ a)|π(D g)` with `y` a
  unit, so `D(t) = D(y) ∧ D(t) = D(y t) = π(D(g a))`), `Locality` (Join over
  the cover `π(D a_i)`), **`is-local`**; **`global`**: the global component
  of `morphism` is `φ`.
- `SpecUnique` (item 3; same data + `psi`, `loc`, `component`): `d-global`
  (`D_⊤(a|⊤) = D a`), `lat-D`, **`lat-eq`** (`ψ = π` pointwise, by
  `ZariskiUniversal.unique`); `chi u = res ∘ ψ♯_u`, `chi-natural`,
  `Basic[g].basic` (`chi = φ_g ∘ eval` on `D g`, via `BasicOpen.extension`
  and Agree); **`sharp-eq`** (`ψ♯` = `π♯` after restriction along `ψ = π`,
  by `Extension.Unique`).
- `SpecUniversal`: **`Hom(X, Spec A) ≅ Hom(A, Γ X)`** as two inverse laws.
  `component psi` (`a ↦ (ψ♯(a|⊤))|⊤`, `component-map` by refl);
  `Of[phi]`: `morphism`, `local`, `component-of` (component = φ);
  `Local[psi,loc]`: `lattice-eq`, `sharp-eq` (ψ is the map of its component).
  Also: `BasicOpen.At.extension` (`extend` as a ring map),
  `Sections.restriction-map`, `Extension.extension-map-at` (refl lemmas).

Step 5 items 1–3 are done (2026-10-29 night). Equality of maps is stated
concretely: lattice maps pointwise, ring maps after the restriction along
`ψ u = π u` (a map's ring part lives over its own lattice map, so no
transport of the record is needed).

- `Slice` (`Over[L,X,e]`): **the restriction `X|e`**. `Opens` = `u ≤ e`
  (`inc`, `below`, `ext`), the lattice with top `e`, `le-inc`/`le-in`,
  `join-inc`; `sheaf` keeps the rings and restrictions of X; `Glue` (a cover
  in `X|e` is one in X; compatibility moved across witnesses by `res-irr`),
  `is-sheaf`; `Inv` (the invertibility open of X, `d-inc` by refl), `inv`,
  `zero-law`, `add-law`, **`restricted`**. The inclusion: `cut u = u ∧ e`,
  `cut-map` (a lattice map, `DoubleLattice.join-d`/`meet-d`), `down`
  (restriction), `natural`, **`inclusion`**, `local-le` (InvOpen.Restrict),
  **`inclusion-local`**. `meet-d-twice`, `meet-d` moved from `Chart` to
  `DoubleLattice` (they depend only on `L`, `d`).
- `Iso` (`Maps[L,M,F,G]`): `IsIso` (lattice map and every `π♯_u`
  bijective), `lat-equiv`, `sharp-equiv`; `injective`; `Units.reflect` (a
  bijective ring map reflects units); **`Local.local`: an isomorphism is
  local**.
- `ChartIso` (`Over[L,X,d]`): **`X ≅ X2|e` and `X ≅ X2|e2`**. `lat1`
  (`u ↦ iota u`, `iota-bot`, `iota-top`), `sharp1 = Chart.to`, `natural1`,
  `chart1`, `lattice-equiv1` (inverse: first component), `sharp-equiv1`
  (inverse: left component), `iso1`, `local1`; the same with `2` (iota2,
  to2, second/right components).

Next 1 is done (2026-10-30): the slice, the inclusion as a local map, the
charts as isomorphisms.

- `DistLattice`: `identity`, `compose` of lattice maps (`hmap-identity`,
  `hmap-compose` by refl).
- `Iso` (additions): equivalences — `equiv-compose`, `equiv-homotopy`,
  `equiv-cancel` (g f and g equivalences ⇒ f), `TwoOfSix` (`middle`,
  `first`); `Inverse[A,B,k,eq]` (`inverse` of a bijective ring map is a
  ring map; `right`, `left` stated with `map inverse`); `EqualOpens` (fact
  1: restriction between equal opens is bijective, by `res-id`/`res-comp`);
  `Maps.Transfer[pi,pi2,lat-eq,le,sharp-eq]` (fact 2: `forward`,
  `backward`, in the form `SpecUnique` produces).
- `Compose`: `Identity[L,F]` (`identity`, `fixes` by `res-id`, `local`,
  `iso`); `Maps[L,M,N,F,G,H].Of[rho,pi]`: `composite` (ring maps typed at
  `ρ(π u)`, `sharp-map` and `restrict-composite` by definition), `Local`
  (composites of local maps), `iso` (composites of isomorphisms);
  `Inverse[..,pi,rho,rp,pr].iso`: π is an isomorphism when ρ∘π and π∘ρ are
  (two out of six, lattice and ring maps).
- `SpecHom`: `Over[B..,A..,beta]`: **`Spec β`** (`morphism`, `local`,
  `global`), `Then[M,X,psi].component`: the global component of `ψ ∘ Spec β`
  is `component ψ ∘ β`. `Retract[..,beta,gamma,ret]`: `γβ = 1` ⇒
  `Spec γ ∘ Spec β` is an isomorphism (it and the identity both agree with
  the map of `b ↦ b|⊤` by `SpecUnique`; `Transfer` forward then backward).
  **`Isomorphism[..,beta,gamma,ret,sec].iso`**: Spec of a ring isomorphism
  is an isomorphism (`Compose.Inverse`), no fractions analysed.
- `AffineCriterion` (`Over[M,X]`): `canonical` = `SpecUniversal.Of[id].morphism`
  with the fractions of `Γ X` (`Affine`), **`IsAffine`** = `IsIso canonical`.
  `Criterion[A..,psi,iso]` (ψ : X ≅ Spec A, any localisation family for A):
  `alpha-equiv` (the global component `UA.component ψ` is bijective:
  `Global.iso`, `ψ♯_⊤`, `EqualOpens`), `Inv` (its inverse ring map), `SH`
  (`Spec(α⁻¹)` iso), candidate `T.C.composite` = `ψ ∘ Spec(α⁻¹)`, iso and
  local, global component `α α⁻¹ = 1`; `SU` (`SpecUnique` with φ = id);
  **`affine : IsAffine`** by `Transfer.forward`.

- `Qcqs` (`Over[M,X]`): `AffineOpen u` = `X|u` affine (`Slice` +
  `AffineCriterion.IsAffine`); `AffineCover` (sig: `count`, `opens`,
  `covers : ⋁ opens = ⊤`, `affine`); **`IsQcqs`** = `∥AffineCover∥`.
  `Two[u,v,covers,au,av]`: two affine opens with `u ∨ v = ⊤` (`opens`,
  `affine` by split on `Fin 2`, `join-two` by refl, `cover`, `qcqs`).
- `DoubledLineQcqs` (`Over[k,setk]`, any ring k): `affine1`, `affine2`
  (`ChartIso.chart1/iso1`, `chart2/iso2` + `AffineCriterion.Criterion` with
  the fractions of `k[X]`), `covers` (`e ∨ e2 = (⊤ ∨ D X, D X ∨ ⊤) = ⊤`),
  **`qcqs`**: the doubled-origin line is a qcqs scheme.

- `PolynomialCoefficients` (symlink to `sag/pn`): `variable-regular` (X is a
  non-zero-divisor of `k[X]`).
- `DoubledLineGlobal` (`Over[k,setk]`, any ring): `Kernel[a,b,e].equal`
  (`f_X : k[X] → k[X][1/X]` injective: elementary kernel + `Regularity` of
  `X^n`); `separate` (global sections of Spec k[X] are determined by their
  component at `D X`); **`equal-components`** (a global section `(s,t)` of the
  doubled line has `s = t`: compare at `D X ≤ ⊤ ∧ D X` through the agreement);
  **the canonical isomorphism** `diagonal : k[X] → Γ`, `a ↦ (a|⊤, a|⊤)` (by
  `FibreProduct.Lift`, agreement by `res-irr`), `back`, `iso`.
- `DoubledLineNotAffine` (`Over[k,setk]`): `Diag`, `diag-joins` (projections
  preserve finite joins); `d-diagonal` (`D_⊤(r)` diagonal, by
  `equal-components` and `Doubling.d-first/d-second`); `image-D`,
  `Image[y].diagonal` (every `π y` diagonal, through a merely given
  presentation of `y` and `PM.preserves`); `at-zero` (`1 = X q` ⇒ `1 = 0` in k,
  evaluation at 0); `IfAffine[aff].one-zero` (the chart `e` is `π y`, so
  `⊤ = D X`, `Bridge.le-below` at `h = 1`); **`not-affine`**: if `1 ≠ 0` in k,
  the doubled-origin line is not affine. The Zariski lattice of `Γ` is never
  compared with that of `k[X]` (review of 2026-10-30).

- `RingedLattice` (addition): `Sheaf.Two[m,m0,m1,le0,le1,covers]`, binary
  covers: `Agree` (on `m0 ∧ m1`), `agree-below` (then on every `w` below
  both), `glue`, `matches0`/`matches1`, `separated`; `Lift[T,h0,h1,e].lift`:
  gluing two ring maps agreeing on the overlap gives a ring map (the sheaf
  analogue of `FibreProduct.Lift`). `DistLattice.Order`: `meet-bot`,
  `join-interchange`, `meet-join-below`, `meet-joins-below` (four cross terms).
- `Fold` (`Over[L,X,d]`): **the fold map** `X2 → X`: `diag u = (u, u)`,
  `lat`, `sharp u : s ↦ (s, s)` (by `Lift`, agreement by `res-irr`),
  `left-sharp`/`right-sharp` by refl, `natural`, **`fold`**, **`local`**
  (`D2(s, s) = diag(D s)`).
- `IntoDoubling` (`Over[L,Y,d,M,X,f,u0,u1,covers,overlap]`, f any map
  `X → Y`, `u0 ∨ u1 = ⊤`, `u0 ∧ u1 = f*(d)`): **the map ψ : X → Y2**.
  `cross0`/`cross1` (below `f*(d)` and `f*(a)`, below `f*(b)`); lattice
  `image x = part0 x ∨ part1 x`, `part0 (a,b) = u0 ∧ f* a`; `image-bot/top/join`,
  `Meet[x,y].image-meet` (antisymmetry, four cross terms); `lat`. Sections:
  `At[x].sec0/sec1` (`f#(s)|part0`, ring maps), `agrees` (on `part0 ∧ part1
  ≤ f*(mid x)`, f natural), `sharp-at` by `Two.Lift` (sections go OUT of the
  doubled ring); `restrict0`/`restrict1` (below `part_i`, ψ# is f#);
  `Natural` (separation on the parts of ψ y); **`psi`**;
  **`Local[floc].local`** (`p_i ∧ D(ψ# z) = p_i ∧ D(f#)` by `InvOpen.Restrict`
  and uniqueness).
- `DoublingUniversal` (`Over[L,Y,d,M,X]`): **`Hom(X, Y2) ≅ {(f, u0, u1)}`**
  as two inverse laws in the concrete convention. `e-join`, `e-meet`,
  `decompose` (`x = (e ∧ (a,a)) ∨ (e2 ∧ (b,b))`). `Of[psi]`: the triple
  (`C.composite = fold ∘ ψ`, `ψ e`, `ψ e2`, `covers`, `overlap`, `local` by
  `Compose.Local`), and law 1 (`lat-eq`, `le`, `sharp-eq`: the map of the
  triple is ψ; separation on `ψ(y0), ψ(y1)`, `ψ` natural, `agree0/1`:
  `(s,s)|y0 = (s,t)|y0`). `From[f,u0,u1,..]`: law 2 (`lat-eq`: `(fold ∘ ψ)*a
  = f* a`, `sharp-eq` by separation on the parts), `chart0`/`chart1`
  (`ψ*(e) = u0`, `ψ*(e2) = u1`).

Next 4, interface (a) is done (2026-10-30): the fold map and the universal
property of the doubling, both inverse laws, locality in both directions.
Not yet stated: the bijection of sets (relate the concrete equality to
equality of `Maps.Ringed` first).

- `MapEquality` (`Maps[L,M,F,G]`, review of Next 4 (a)): `Total` (Σ of the
  parts; `from-to` by `split`, no record η), **`set`** (maps form a set),
  `SharpEq`, `total-ext` (one path induction on the lattice map; refl case
  `res-id`), **`ext`** (the concrete equality of `SpecUnique`/`Transfer`
  gives equality of records), `Local[DF,DG]`: `local-prop`, `LocalMap`,
  `local-set`, `local-ext`. `DistLattice.HomProperties`: `set`, `ext`.
- `DoublingUniversal` (additions): `Triple`, `triple`, `map-of`, `law1`,
  `Back[t].fold-eq`/`law2`, **`equivalence`** (maps X → Y2 ≃ triples),
  `LocalTriple`, **`local-equivalence`** (local maps ≃ triples with f local).
- `Global.d-global` (moved from `SpecUnique`); `SpecUniversal`:
  `morphism-component`, `local-map`, **`equivalence`** (local maps
  X → Spec A ≃ ring maps A → O_X(⊤)).
- `Compose.Assoc.assoc`; `SpecHom.Precompose` (`gamma` = Γ(ρ),
  `component`: the global component of ρ∘ψ is Γ(ρ)∘(component ψ)).
- `DoubledLinePoints` (`Over[k,setk,B,setB,iota]`, milestone 1): `OverK`
  (the component of fold∘ψ restricted to k is `iota-top`), `Points`,
  `Coordinates` = {(t,u0,u1) | u0 ∨ u1 = ⊤, u0 ∧ u1 = D t}, `support`
  (`f*(D X) = D_⊤(φ X)`), `Forth`, `Back` (φ from `Universal`, f from
  `SpecUniversal.Of`, ψ from `IntoDoubling`), `ForthBack`, `BackForth`,
  **`equivalence : Points ≃ Coordinates`**.
- `DoubledLineBaseChange` (`Over[.., B2, iota2, h, over]`): `zar-D`
  (`Zar(h)(D b) = D(h b)`), `Pull[p].point` (ψ∘Spec h: local, over k by
  `Assoc` + `Precompose` + `SpecHom.global`), `coordinate-eq` (h t),
  `Image`, **`natural`**: coordinates(ψ∘Spec h) = (h t, Zar(h) u0, Zar(h) u1).

Next 4 milestone 1 is done (2026-10-30), with base change.

Milestone 2 (after the 2026-10-30 entries; the plan of the review, all checked first try
except one hidden argument and one reserved word; 87 modules 2.1 s):
- `DistLattice` (additions): `Complements[D]` (`Complementary`, `Pairs`,
  `complementary-prop`, `pair-ext`, `exchange`), `ComplementMaps[D,E,h].image`,
  `ComplementIso[D,E,h,k,kh,hk].equivalence`; `SupportMaps.Pull` (ring map
  then support) and `SupportAfter` (support then lattice map).
- `Idempotents`: `Laws[A]` (`IsIdem`, `comp e = 1 − e`, `orthogonal`,
  `sum-comp`, `unit-idem`, `zero-of-unit`), `Idems[A,setA]`, `Map` (ring maps
  preserve `1 − e`, idempotents), `Transfer` (a ring iso carries idempotents
  bijectively). `On[M,X]` for **any locally ringed lattice**: `d-restrict`
  (`D_w(s|w) = w ∧ D(s)`), `forth e = (D e, D(1−e))`, `trivial` (G(w) trivial
  for `w ≤ ⊥`: separation for the empty cover), `Reading` (`s|u = 1`,
  `s|v = 0` ⇒ `D s = u`), `Back` (glue 1 on u with 0 on v by `Sheaf.Two`),
  **`equivalence : Idem(G ⊤) ≃ complementary pairs`**.
- `Interval` (`Up[M,a]`): the lattice `[a, ⊤]`, `r = a ∨ −` a lattice map,
  `r-on`, `determined`; `Splittings` (u ∨ v = ⊤, u ∧ v = a) ≃ complementary
  pairs of the interval (`splittings`).
- `PrincipalQuotient` (symlink to `jacobian/`, with `PrincipalCertificates`
  from `presentations/`): B/(t).
- `ZariskiQuotient` (`Over[B,setB,t]`): `Represent[N,d,sd,kills]` (the
  interval is the universal support killing t: `factor`, `factor-D`,
  `unique`), `Descend` (supports killing t descend to B/(t)), `alpha`, `beta`
  and the two inverse laws (`Zar(B/(t)) ≅ [D t, ⊤]`, by the two universal
  properties, no lifts chosen); **`splitting : Idem(B/(t)) ≃ Splittings`**
  (Global + Idempotents + the iso + Interval); `Formula[b,hb]`: the
  splitting of q(b) is `(D t ∨ D b, D t ∨ D(1−b))`.
- `DoubledLineIdempotents`: `Data = Σ (t : B), Idem(B/(t))`, `coordinates`
  (regrouping is the identity on components), **`equivalence : Data ≃
  Points`**, i.e. `Hom_k(Spec B, S) ≃ Σ t, Idem(B/(t))`.
- `DoubledLineIdempotentsBaseChange`: `QuotientMap` (h̄ : B/(t) → B2/(h t)),
  `At.agrees` (by quotient induction, from `Formula` and `zar-D`),
  `coordinates-image`, **`natural`**: the point of (t, e) followed by
  Spec h is the point of (h t, h̄ e).
Checker observations (≤ 0.04 s each, left as is): `DoubledLineIdempotents.
idempotent-coordinates` opens `Interval.El` 35 times (writing the η-step of
the splitting as a refl lemma did not change it);
`DoubledLineIdempotentsBaseChange.coordinates-image` opened `image` 148 times
until its by-definition step `coordinates-of-image` was stated (now 7).

Next 5 prerequisite (done): `(Spec A)|_{D(g)} ≅ Spec(A_g)` as locally
ringed lattices, by universal properties only (no fraction is analysed):
- `SliceUniversal`: maps out of X|e (ringed convention) are the maps out of X
  sending e to ⊤: `Back` (factorisation, local when the map is), `factor-cut`
  (`back(π) ∘ cut = π`), `Restore` (`back(ρ ∘ cut) = ρ`), `cancel`
  (`ρ ∘ cut = ρ₂ ∘ cut ⇒ ρ = ρ₂`).
- `SpecUniversal.unique`: two local maps with the same global component are
  equal; `Global.extend-global` (moved from `SpecUnique.Basic`, one name):
  `extend(f_g a) = (a|⊤)|D g`; `Slice.res-inc` (restriction in X|e is that of
  X, by definition).
- `SpecBasicOpen`: j : Spec(A_g) → X|D(g) is the factor of Spec β
  (β = f_g; Spec β sends D g to D(β g) = ⊤, a unit), k : X|D(g) → Spec(A_g)
  the map of `extend : A_g → O(D g) = Γ(X|D(g))`. Both composites are
  identities: `jk` by `SpecUniversal.unique` (global component Γ(j) ∘ extend
  = x ↦ x|⊤, `Localisation.Agree` on β a); `kj` after cut (`Compose.Assoc`,
  `SpecUniversal.unique`, then `SliceUniversal.cancel`). Hence `j-iso`,
  `k-iso` (`Compose.Inverse`) and `affine` (X|D(g) is affine,
  `AffineCriterion`). All checked first try; `segc qcqs all`: 89 modules,
  0 failed, 2.4 s.
Checker observations (≤ 0.07 s each, left as is): typing Γ(X|e) as
`Sl.sheaf.ring Sl.topS` instead of the consumers' `Sl.restricted.sheaf.ring
Sl.lattice.top` opened `Slice.topS`/`inc` 666 times in `gamma-phi`;
declaring φ once at that type (`phi`) brought it from 7613 to 1616
comparisons. `cut-component` opened the Zariski lattice 679 times until the
by-definition step `Slice.res-inc` was written as a middle point (129).
The rest is `Affine.spec`/`SpecLocal.spec`/`Sheaf.structure` reshuffling as
in `SpecHom`, remaining with the current interfaces (reviewer: not worth
further restructuring).

Next 5 step 1 (done, per the review of the prerequisite): L = k[X][1/X],
x = f_X(X).
- `Inversion`: τ : k[X] → L fixing k, X ↦ x⁻¹ (`Universal.Given`); x⁻¹ a
  unit, so τ extends uniquely to σ : L → L (`LH.universal`); `sigma-k`,
  `over-k` (σ fixes k, exposed for the gluing over k); `sigma-x` (σ x = x⁻¹),
  `sigma-x-inv` (by `inverse-unique`); `twice-f` (σ² ∘ f = f by
  `Universal.unique` twice), `involution` (σ² = 1, `Localisation.Agree`),
  `sigma-sigma`.
- `PuncturedChart`: Spec σ an automorphism of Spec L
  (`SpecHom.Isomorphism`), and `automorphism` of (Spec k[X])|D(X) =
  j ∘ Spec σ ∘ k (ringed composite of `SpecBasicOpen.j`, Spec σ, `k`), with
  `iso` and `local`. All first try; ≤ 0.01 s per declaration. Clean stopping
  point before gluing with a transition (step 2).

Next 5 step 2 (done, per the review of step 1; all checked first try;
`segc qcqs all`: 95 modules, 0 failed, 2.6 s):
- `LatticePullback` (`Over[L1,L2,M,f,g]`): the opens `{(u, v) | f u = g v}`
  for any two lattice maps, componentwise lattice (`DoubleLattice` is the case
  f = g = − ∧ d); projections `first-map`/`second-map`, `le-pair`, `join-first`.
- `GlueAlong` (`Over[L1,L2,M,X1,X2,Y,phi1,phi2,local1,local2]`): the gluing
  of two locally ringed lattices along LOCAL maps φᵢ, written in the
  ringed-lattice convention (lattice maps pᵢ : Lᵢ → M, φᵢ♯ : Oᵢ(u) →
  O_Y(pᵢ u)); geometrically φᵢ : Y → Xᵢ, Y the overlap. Built
  alongside `Doubling` with the same proofs: opens in the pullback of p1, p2;
  sections `O1(u) ×_Y(p1 u) O2(v)` with `φ1♯ s = (φ2♯ t)|mid` (`leg2`:
  φ2♯ then restriction to the equal open `mid = p1 u`); restriction by
  naturality of φ1, φ2; sheaf componentwise, agreement by separation in Y on
  the cover `p1 u_i`; `D(s,t) = (D s, D t)`, in the pullback by locality of
  φ1, φ2 and `InvOpen.Restrict`; **`glued`**. The plan's orientation is the
  instance below; stating it for any two local maps made the proof use only
  the map interface (no slices inside).
- `FibreProduct.LeftEquiv`/`RightEquiv`: if the other leg is bijective, the
  projection is. `Iso.Invert`: the inverse of an isomorphism of ringed
  lattices (lattice inverse a lattice map by injectivity; ρ♯_m = (π♯)⁻¹ ∘
  restriction to the equal open π(b m); naturality after the injective π♯),
  `inverse-iso`.
- `GlueTransition` (`Over[L,X,d,theta,theta-local,theta-iso]`): Y = X|d,
  φ1 = `Slice.inclusion`, φ2 = θ ∘ inclusion (`Compose`, local); opens
  `u ∧ d = θ*(v ∧ d)` (as slice elements). `e1 = (⊤, d)`, `e2 = (d, ⊤)`,
  `covers`. Charts as the INVERSES of the projections (no inverse of θ is
  built as a map): `First.proj` (`(u,v) ↦ u`, `(s,t) ↦ s`) is an iso —
  lattice inverse `u ↦ (u, θ*⁻¹(u ∧ d))` from `theta-iso`'s section, rings by
  `LeftEquiv` since `leg2` = restriction ∘ θ♯ ∘ restriction between equal
  opens; `Second.proj` likewise with `RightEquiv` (θ need not be invertible
  there); `chart = Iso.Invert.inverse`, `chart-iso`, `local` (`Iso.Local`).
- `ProjectiveLine` (`Over[k,setk]`): θ = `PuncturedChart.automorphism`;
  **`projective-line`**, `affine1`/`affine2` (`AffineCriterion` on the two
  charts), **`qcqs`** (`Qcqs.Two`). This also covers item 3 below.
Not done (not in the stopping point): the structure map ℙ¹ → Spec k
(glues since σ fixes k, `Inversion.over-k`); maps into the glued object.
Checker observations (≤ 0.03 s per declaration, left as is): `GlueAlong`
opens at most 34 distinct definitions per declaration (`Glue.unique`), the
pattern of `Doubling`; `ProjectiveLine.Q` pays the one-time comparison of the
pullback lattice record (`pair`*50), as `DoubledLineQcqs.Q`;
`ProjectiveLine.GT` compares `PuncturedChart`'s slice instance with
`GlueTransition`'s (`Slice.lattice`*37).

Next 5 step 4 (done, per the review of step 2; all checked first try bar
one missing import; `segc qcqs all`: 98 modules, 0 failed, 2.6 s):
`Γ(ℙ¹_k) ≅ k` for every commutative ring k.
- `Compose.Gamma` (Γ(ρ) = restriction to ⊤ after ρ♯_⊤) and
  `Compose.Maps.Of.gamma-composite` (Γ(ρ∘π) = Γρ ∘ Γπ: res-comp, ρ natural).
  `SpecHom.Precompose.gamma` is now this Γ (one name; `gamma-phi` 628 → 284
  openings, the rest unchanged).
- `VariableKernel`: injectivity of f_X : k[X] → k[X][1/X], moved out of
  `DoubledLineGlobal` (which now uses it) so that ℙ¹ does not depend on the
  doubled line.
- `PuncturedChart.gamma-automorphism`: Γ(θ)(φ y) = φ(σ y), φ = extend :
  L → O(D X), by functoriality of Γ through θ = k ∘ Spec σ ∘ j and the three
  known components (`gamma-j` from `SpecBasicOpen.gamma-phi`, `gamma-sigma`
  = `SpecHom.global`, `gamma-k` = component of the map of φ). Pointwise, no
  `Localisation.Agree` needed.
- `InversionOverlap` (key lemma): `f(p) = σ(f(q)) ⇒ p = q = coef₀(p)`.
  Deviation from the review's plan, same idea one coefficient at a time:
  induction on a coefficient list of q (the statement is a proposition);
  q = c + X q' (`horner`) gives f(X(p − c)) = τ(q'), so by induction
  X(p − c) = q' is a constant with constant coefficient 0
  (`PolynomialCoefficients.shift-coef`), hence p = c (X regular) and q = c.
  No reversal polynomial and no coefficients above n.
- `ProjectiveLineGlobal`: the gluing equation at ⊤, restricted to the equal
  open d (`to-d`, injective by `Iso.EqualOpens`): `left-trace` (component
  of the inclusion, `SpecBasicOpen.cut-component`), `leg2-d` (res-comp),
  `component-theta` (`SpecHom.Precompose`), `right-trace`
  (`gamma-automorphism`); `overlap` (a section has f(a) = σ(f(b))),
  `agree-back` (conversely); `diagonal` (k → Γ, a ↦ (a|⊤, a|⊤), by
  `FibreProduct.Lift` and `Inversion.sigma-k`), `back` (coef₀ of the first
  polynomial), **`iso`**.
Checker observations (≤ 0.15 s per declaration, left as is):
- `right-trace` opened `PuncturedChart.automorphism` 3612 times while
  `gamma-automorphism` was stated with `C2.GC.gamma` (Γ of the composite on
  `Sl.sheaf`) and used at `Precompose`'s Γ(automorphism) on
  `Sl.restricted.sheaf`; stating it at the consumer's instance
  (`PuncturedChart.GA`, one `refl` to `C2.GC`) and writing `leg2-d` at the
  pullback's own point `PB.second ⊤` (not `ZA.top`, its value) took
  `right-trace` from 12295 to 1198 openings. Likewise `left-trace` at
  `PB.first ⊤`: `overlap` 986 → 480, `agree-back` 1747 → 884. The rest is the
  `spec`/`structure`/`restricted` reshuffling recorded for `SpecHom`.
- `InversionOverlap.Step.expand`/`difference` (≈ 570 each, 0.02 s) open
  `PolynomialRing.Extension.ring` and `Affine.Loc` once per step of a calc in
  L, as `Inversion.sigma-x-inv` does; naming the constant at `P.ring.R` did
  not change it.

Review of step 4: the coefficient-list induction accepted (needs only the
constant coefficient of X r, regularity of X and injectivity of f_X; works
over any ring); `VariableKernel` accepted; the remaining opening counts stay
recorded, no further restructuring. Plan for step 5: the diagonal-image
argument of the doubled-origin line, no k-points, no identification of
Zar(Γ ℙ¹) with Zar(k).

Next 5 step 5 (done, per that review; first try bar one missing `open`;
`segc qcqs all`: 99 modules, 0 failed, 2.5 s): ℙ¹ over a nonzero ring is
not affine.
- `ProjectiveLineGlobal.Back.equal-components`: a global section (s, t) has
  s = t (both are the same constant).
- `VariableKernel.one-zero`: D(1) ≤ D(X) in Zar(k[X]) gives 1 = 0 in k
  (`power-one`, `at-zero`: 1 = X q evaluated at 0), moved from
  `DoubledLineNotAffine`, which now uses it.
- `ProjectiveLineNotAffine` (as `DoubledLineNotAffine`): `Diag`,
  `diag-joins` (`LatticePullback.join-first/join-second`), `d-diagonal`
  (`GlueAlong.d-first/d-second` + `equal-components`), `image-D`,
  `Image.diagonal` (presentations of Zar(Γ)), `IfAffine` (the chart
  `GlueTransition.e1 = (⊤, D X)` is in the image, so ⊤ = D(X), so 1 = 0),
  **`not-affine`**. Every declaration ≤ 0.02 s; `d-diagonal` 164 openings.

Review of step 5: ℙ¹ₖ is qcqs, Γ = k, non-affine for 1 ≠ 0 — the basic
example is complete. Next: the structure map by SpecUniversal on the
diagonal k → Γ(ℙ¹), compatible with Spec(k → k[X]) on both charts by
uniqueness; commit; then the mapping property (below).

Structure map (done, first try; `segc qcqs all`: 100 modules, 0 failed,
2.5 s): `ProjectiveLineStructure`: `structure` = map of `diagonal`
(`SpecUniversal.Of`), local; `First/Second.compatible`: the structure map
after each chart projection (geometrically: on each chart) is Spec(k → k[X])
(`SpecHom.Over[.., P.inclusion]`), by `SpecUniversal.unique`: the global
component is Γ(proj) ∘ Γ(inclusion) ∘ diagonal (`Precompose` twice),
`gamma-inclusion` (restriction from ⊤ to eᵢ, res-comp), then
`GlueAlong.Res.left-res/right-res`, res-comp, res-id, `Dg.left-lift`.
Checker observation (left as is, per review): `gamma-inclusion` opens 3135
definitions in 0.02 s (slice restriction against the glued one); `value`
1527 in 0.1 s.

Next (from the review): the mapping property of ℙ¹. Concretely, a map
X → ℙ¹ is: covering extents u₀ ∨ u₁ = ⊤, sections bᵢ ∈ O(uᵢ), with
u₀ ∧ u₁ = D_{u₀}(b₀) = D_{u₁}(b₁) and b₀ b₁ = 1 on the intersection; these
equalities make the extents the full inverse images of the charts. A
descent theorem; start a fresh session there.

Next 1 (the affine criterion) is done (2026-10-30), following the review:
no fraction is analysed after `SpecUnique`; Spec β is an isomorphism by
identifying both composites with identities.

Next:

1. ~~**Affine criterion, once**~~ (done; plan kept for the record): if `ψ : Spec A ≅ X`, then the canonical map
   `X → Spec ΓX` (`SpecUniversal.Of[id].morphism`, with `Affine` fractions
   for `ΓX`) is an isomorphism. Plan:
   - composition of maps of ringed lattices (and of local maps), the
     identity map; the global component of a composite
     (`component(ψ ∘ Spec β) = component ψ ∘ β`);
   - `Spec β` for a ring map `β : A' → A` = `SpecMap` with `X = Spec A`,
     `φ = global ∘ β`; for a ring isomorphism `β`, `Spec β` is an isomorphism
     (lattice part by `ZariskiUniversal.unique`, ring part by `Agree` on
     basic opens and `Extension.Unique`);
   - `α = component ψ` is a ring isomorphism (`Global.iso`, `ψ♯_⊤`,
     restriction between equal opens); the canonical map and `ψ ∘ Spec α⁻¹`
     are local with component `id`, so they agree (`SpecUnique`), and an
     isomorphism transfers along that agreement.
   Review of 2026-10-30 (accepted plan; follow it):
   - directions, geometric notation: `ψ : X ≅ Spec A`, `α : A ≅ ΓX`; the
     candidate is `X →ψ Spec A →Spec(α⁻¹) Spec ΓX`, global component
     `α α⁻¹ = 1`, so `SpecUnique` identifies it with the canonical map (in
     the ringed-lattice convention the composition order is reversed);
   - intermediate fact 1: restriction between equal opens is a ring
     isomorphism, directly from `res-id`/`res-comp`;
   - intermediate fact 2: `IsIso` transfers across the concrete equality of
     maps (pointwise lattice equality; section maps through those
     restriction isomorphisms);
   - `Spec β` an isomorphism: build `Spec(β⁻¹)` and identify both composites
     with identities by `SpecUnique`; do not analyse the fractions again.
   - Leave the `ChartIso` proof as is; whether its opening count is a checker
     defect needs a separate small example.
2. ~~Both doubled-line charts are affine, and the doubled-origin line is a
   qcqs scheme~~ (done 2026-10-30: `Qcqs`, `DoubledLineQcqs`).
3. ~~Global sections and non-affineness over a nonzero base~~ (done
   2026-10-30: `DoubledLineGlobal`, `DoubledLineNotAffine`; the proof follows
   the review: equal components, diagonal invertibility opens, generators,
   Nullstellensatz at `h = 1`, evaluation at 0).
4. **The points of the doubled-origin line S over k** (review of
   2026-10-30: two milestones; build on the geometric interfaces, never
   return to fraction representatives).

   *Over k, made explicit.* A k-algebra is a ring B with a ring map
   `ι : k → B`; an unrestricted map `Spec B → S` carries no such choice.
   S lies over Spec k through `k → k[X] ≅ Γ S` (`DoubledLineGlobal.diagonal`).
   A k-map `Spec B → S` is a local map ψ (ringed convention `L_S → L_B`)
   whose composite with `S → Spec k` is `Spec ι`; by `SpecUniversal` this is
   the concrete condition that the global component of ψ, restricted to k,
   is ι. No category layer.

   *Milestone 1 (geometric classification).* For k-algebras B,

       Hom_k(Spec B, S) ≅ { (t, u₀, u₁) | u₀ ∨ u₁ = ⊤, u₀ ∧ u₁ = D(t) },

   t : B, u₀, u₁ : L_B. The opens are the **full inverse images** of the two
   charts, `u₀ = ψ(e)`, `u₁ = ψ(e2)`, so the triple keeps no redundant cover
   choice. Forward: on `Spec B|uᵢ` the map into chart i ≅ Spec k[X]
   (`ChartIso`) is a k-map `k[X] → O_B(uᵢ)` (`SpecUniversal` for the slice),
   i.e. a section xᵢ; the charts' overlap is `(D X, D X)`, where both
   coordinates are the same function, so x₀ and x₁ agree on `u₀ ∧ u₁` and glue
   to t ∈ O_B(⊤) = B; locality gives `u₀ ∧ u₁ = ψ(e ∧ e2) = D(t)`. Backward:
   t|uᵢ gives maps into the charts, glued by a universal property of the
   doubling. Interfaces, in order:
   (a) `Doubling`: maps from any X into the doubling ↔ pairs of maps into X
       (on the full inverse images of the charts) agreeing on the overlap —
       lattice part through `L₂`, ring part through `FibreProduct.Lift`;
   (b) restriction of a local map to an open (`Slice` + `Compose`);
   (c) `SpecUniversal` for `X|u` (already general in X);
   (d) the k-condition through global components (`SpecHom.Then`).
   *Sharpened (review of 2026-10-30, supersedes interfaces (a)–(d) above).*
   Interface (a) is a universal property of the doubling, with the overlap
   **exactly** the inverse image of the gluing open (two maps agreeing on an
   overlap are not enough). For the doubling of Y along d, with the fold map
   `Double_d Y → Y`:

       Hom_loc(X, Double_d Y) ≅ { (f, u₀, u₁) | f : X → Y local,
                                  u₀ ∨ u₁ = ⊤,  u₀ ∧ u₁ = f*(d) }

   f = composite with the fold map, uᵢ = the full inverse images of the
   charts. Construction from (f, u₀, u₁):
   - lattice: `(a, b) ↦ (u₀ ∧ f*a) ∨ (u₁ ∧ f*b)`; the overlap condition with
     `a ∧ d = b ∧ d` makes it preserve meets as well as joins;
   - sections go OUT of the doubled ring (not `FibreProduct.Lift`): apply
     f♯ to the two components, restrict to `u₀ ∧ …` and `u₁ ∧ …`, glue in X;
     agreement from the fibre-product equation, uniqueness by separation.
   Order: the fold map first, then this universal property, the two inverse
   laws in the concrete equality convention (as `SpecUnique`); call it a
   bijection of sets only after relating that equality to equality of
   `Maps.Ringed`.
   *(Done 2026-10-30: `Fold`, `IntoDoubling`, `DoublingUniversal`; the
   bijection-of-sets statement is still open.)*
   Milestone 1 then follows for `Y = Spec k[X]`, `d = D(X)`: `SpecUniversal`
   identifies k-maps `f : Spec B → Y` with ring maps `k[X] → B` extending ι,
   i.e. with `t ∈ B`; locality gives `f*(D X) = D(t)`. Restriction of
   arbitrary morphisms is probably not needed.

   Equality of maps as in `SpecUnique` (lattice maps pointwise, ring maps
   after restriction); the triples form a set and the conditions are
   propositions, so the result is a bijection.
   *Base change, part of the statement:* for a k-algebra map `h : B → B'`,
   precomposition with `Spec h` corresponds to
   `(t, u₀, u₁) ↦ (h t, Zar(h) u₀, Zar(h) u₁)`, `Zar(h)` the factor of
   `D ∘ h` (`ZariskiUniversal`).

   *Milestone 2, plan from the review of 2026-10-30 (follow it):* by
   universal properties again.
   - Both `Zar(B/(t))` and the interval `[D(t), ⊤]` represent supports of B
     sending t to bottom. The interval has bottom D(t) and universal support
     `b ↦ D(t) ∨ D(b)`. This gives the lattice isomorphism without choosing
     lifts of quotient elements.
   - Complementary opens ↔ idempotents, by the sheaf: an idempotent e gives
     the pair D(e), D(1−e); conversely, for u ∨ v = ⊤, u ∧ v = ⊥, glue 1 on u
     with 0 on v (`RingedLattice.Sheaf.Two`; they agree on the empty
     intersection). Separation gives e² = e; the support laws recover
     D(e) = u, D(1−e) = v. Uniqueness gives the inverse laws and
     compatibility with ring maps.
   - Combined with `DoubledLinePoints.equivalence`:
     `Hom_k(Spec B, S) ≃ Σ (t : B), Idem(B/(t))`, natural in B
     (`DoubledLineBaseChange`); the zero ring is included automatically.
   *(Done: `Idempotents`, `Interval`, `ZariskiQuotient`,
   `DoubledLineIdempotents`, `DoubledLineIdempotentsBaseChange`.)*

   *Milestone 2 (algebraic simplification).* `Zar(B/(t)) ≅ [D(t), ⊤]`, then
   complementary pairs in `[D(t), ⊤]` (u₀ ∨ u₁ = ⊤, u₀ ∧ u₁ = D(t)) ↔
   complemented elements of `Zar(B/(t))` ↔ idempotents of `B/(t)`. Hence

       Hom_k(Spec B, S) ≅ Σ (t : B), Idem(B/(t)),   natural in B.

5. `P¹` (gluing along an isomorphism of opens, `X ↦ X⁻¹`; generalise
   `Doubling` only then).
   *Plan from the review of milestone 2 (follow it; start a fresh session
   here).* Review: the doubled-origin example is complete through its
   natural functor of points; the reusable idempotent theorem is useful
   beyond it; the `Interval.El` openings do not warrant restructuring.
   Prerequisite: `(Spec A)|_{D(g)} ≅ Spec(A_g)` as locally ringed lattices
   (`BasicOpen` only identifies the section rings); it also serves later
   descent arguments. *(Done: `SliceUniversal`, `SpecBasicOpen`.)* Then, in
   bounded steps:
   1. ~~the overlap involution of `k[X,X⁻¹]`, `X ↦ X⁻¹`, its own inverse by
      polynomial and localisation uniqueness~~ (done: `Inversion`,
      `PuncturedChart`; review plan: τ by the polynomial universal property,
      σ its unique extension, σ(x) = x⁻¹ and σ(x⁻¹) = x by uniqueness of
      inverses, σ² = 1 by polynomial uniqueness and `Localisation.Agree`;
      expose that σ fixes k; then SpecHom + the principal-open isomorphism
      give the automorphism of the punctured chart);
   2. ~~glue with this transition: a version of doubling with a non-identity
      overlap automorphism (no general gluing of schemes yet)~~ (done:
      `LatticePullback`, `GlueAlong`, `GlueTransition`, `ProjectiveLine`);
      *Plan from the review of step 1 (follow it; start a fresh session
      here).* Build the gluing ALONGSIDE `Doubling`, reusing its
      componentwise lemmas (`FibreProduct`, `DoubleLattice`, `Sheaf.Two`, …);
      do not migrate the existing doubling proofs.
      - Orientation, fixed explicitly: θ : X|d → X|d an automorphism with
        inverse-image map θ* (ringed convention, as `PuncturedChart.
        automorphism`). Opens
        `L_θ = {(u, v) | u ∧ d = θ*(v ∧ d)}`; sections over (u, v) are pairs
        (s, t) with `s|_{u∧d} = θ♯_{v∧d}(t|_{v∧d})`. The section ring is
        again a fibre product; the sheaf condition is componentwise;
        compatibility of invertibility opens now uses locality of θ.
      - Then the two chart isomorphisms (as `Chart`/`ChartIso`), the affine
        criterion on each chart, and qcqs schemehood (as `DoubledLineQcqs`).
        For ℙ¹_k use θ = `PuncturedChart.automorphism`.
      - Difference from doubling: the doubling universal property in its
        global-fold form does NOT carry over. With inversion as transition
        the two chart coordinates do not glue to one map into 𝔸¹, so there is
        no coordinate fold ℙ¹ → 𝔸¹. Maps into the glued object are pairs of
        local chart maps agreeing through the transition. The structure map
        to Spec k does glue, since σ fixes k (`Inversion.over-k`).
      - Stopping point: the glued locally ringed lattice, its two affine
        chart isomorphisms, and its qcqs witness.
   3. ~~identify both charts, P¹ is a qcqs scheme~~ (done with step 2:
      `ProjectiveLine.affine1/affine2/qcqs`);
   4. ~~`Γ(P¹) ≅ k`: `p(X) = q(X⁻¹)` forces both constant~~ (done:
      `InversionOverlap`, `ProjectiveLineGlobal`; see the step 4 entry above);
      *Plan from the review of step 2 (follow it; start a fresh session
      here).* Key lemma, over any commutative ring (zero ring included):
      `f_X(p) = σ(f_X(q))  ⇒  p = q = a` for a unique constant `a ∈ k`.
      No general Laurent-polynomial library. Proof:
      (1) write `q = Σ_{j≤n} q_j X^j` (finite coefficient representation,
          `PolynomialCoefficients`);
      (2) multiply the overlap equation by `X^n`:
          `f_X(X^n p) = f_X(Σ_j q_j X^{n−j})`;
      (3) injectivity of `f_X` (already proved) gives equality in k[X];
      (4) comparing coefficients above n, every positive coefficient of p
          vanishes;
      (5) apply the involution for the same conclusion on q; the constants
          agree.
      Then expose the canonical isomorphism `k → Γ(P¹_k)`, `a ↦ (a, a)`,
      with inverse: evaluate either polynomial component at 0. Bounded step;
      the structure map and non-affineness come after.
   5. ~~not affine for `1 ≠ 0` in k, by the canonical affine criterion~~
      (done: `ProjectiveLineNotAffine`; see the step 5 entry above).

Checker observations (0.00 s each, recorded; reviewer: leave them alone, no further abstraction):
- writing `RingedLattice[l].On[Dbl.DD.lattice]` afresh in a client instead
  of `Dbl.R2`/`Dbl.LR2` makes one comparison open the doubled lattice
  record field by field (its laws included); using the module names of
  `Doubling` avoids it (`DoubledLine`);
- in `Chart`, the first declaration stating `OD.Le` (`iota-le`) pays the
  same one-time comparison, whichever instance path `DD` takes.
- `SpecUnique.d-global` (0.01 s) opens the Zariski quotient about 30
  times: `a|⊤` is used as a section over `D 1` (`SpecInv.Basic` at `g = 1`),
  and `IsInvOpen ⊤` is compared with `IsInvOpen (D 1)`. Moving the
  fraction along a refl lemma did not reduce it (34); left as is.
- comparing two proofs of `⊤ ≤ π ⊤` opens their whole construction
  (`SpecUniversal.component-of`: 48); switch witnesses with `GO.res-irr`
  instead (13).
- `ChartIso`: comparing the slice's section ring `S1.sheaf.ring (hmap lat1 u)`
  with `Dbl.ring (iota u)` in one step opened `iota` about 1700 times (9000
  in `chart1`), although each of the three definitional steps (slice sheaf →
  doubled sheaf → `Dbl.ring (inc ..)` → `Dbl.ring (iota u)`) opens at most 10
  alone. Typing `sharp`, `natural` and the equivalences at the middle point
  `Dbl.ring (S1.inc (hmap lat1 u))` brings it to 146 (`natural1`, where
  `Chart.natural` is stated with `iota`). A checker question, not a proof
  defect.

- `SpecHom.Over.Then`: comparing `(ρ∘π) u` with `ρ(π u)` inside the
  Zariski instance opens the lattice laws (radicals, truncation; 21
  definitions for one `refl`), while the same comparison in `Compose`
  (generic lattices) opens 3. So the definitional facts of a composite are
  stated in `Compose` (`restrict-composite`, `Identity.fixes`) and used by
  name; with them the quotient is not opened.
- Writing the middle point of a two-step `trans` as a `calc`
  (`AffineCriterion.Criterion.component`) took it from 16 openings to 0;
  aliases (`p`, `y`, `alpha`, `candidate`, `composite`) were removed for the
  same reason (rule 2).
- Remaining openings in `SpecHom` (`Then.component` 13–15, `global` 13,
  `Retract.map-iso` 15) are `SpecLocal.spec.sheaf` against
  `Sheaf.structure` (equal by definition): maps out of `Spec A` are typed
  from `structure`, maps into `Spec A` (as an `X` of `SpecUniversal`) into
  `spec.sheaf`, and `Spec β` is both. Typing either side the other way only
  moves them (tried: up to 50). Left as is (0.05 s).

- `DoubledLineQcqs.Q` (instance `Qcqs.Over[DD.lattice, doubled]`) pays the
  one-time comparison of the doubled lattice record recorded for `Chart`
  (`pair`*50); using `Dbl.DD.lattice` instead does not help. Left as is.

- `DoubledLineNotAffine`: Γ must be written as `AffineCriterion`'s
  `Dbl.doubled.sheaf.ring DD.lattice.top` (its `ZG`, `Can`); written as
  `Dbl.ring DD.topD` instead, every comparison unfolded the doubled lattice
  record to reach `top` (`lat-equiv`/`e-diagonal`: 17127 openings, 0.08 s;
  now 7). The two names meet once, in `d-diagonal` (199), where
  `DoubledLineGlobal.equal-components` is applied.
- `DoubledLineGlobal`: `Dbl.left DD.topD z` lives in `O(first topD)`, used as
  `S.Section ⊤`; `back-diagonal` opens `first`/`pair`/`topD` 116 times (228
  before writing its middle point). Left as is (0.01 s).

- `Fold.fold`: with `sharp`/`natural` typed at `diag u`, building the
  record compared them with the field types at `DL.hmap lat u` by opening
  `pair`/`diag` 9090 times; typed at `DL.hmap lat u` it is 112. Likewise
  `Fold.local` written with `fold.lat`/`fold.sharp` (859 → 6 openings of
  `fold`).
- `DoublingUniversal.From.Sharp.on0/on1` (0.02 s) compare `(fold ∘ ψ)*(a)`
  with `image (diag a)` and `part0 (diag a)` with `u0 ∧ f* a` (definitional):
  `pair`/`diag` 139 times each (242 before writing the middle point);
  `Of.Sharp.on0/on1` similarly (`pair`/`diag` 128). Left as is.

- `DoubledLineBaseChange` (0.15 s, at most 0.06 s per declaration): the
  openings are `Affine.spec`/`SpecLocal.spec`/`Sheaf.structure` reshuffling
  as in `SpecHom`; `Pull.gamma-global` (`SpecHom.global` used through
  `Precompose.gamma`) opens `MonoidFractions.Fraction` 48 times comparing
  the two instances of `Global`. Left as is.

Locks: leave `lattice` (ZariskiLattice) transparent. Clients opening it to
`Quotient.Quot.Q` is not by itself a defect; lock it only if a small trial
(as in `core/`) shows clearer dependencies without bookkeeping spreading into
clients. The lock on `inv-map` stays: later proofs use its defining
property, not its construction.

Step 3 items 0–5 are done (2026-10-29): naturality of evaluation,
presentations behind the lattice interface, separation on arbitrary opens,
amalgams one component at a time, and the sheaf property for all finite
covers. The empty cover needs no separate treatment (n = 0), and no
induction on covers was needed: a refinement of `⋁ u_i` reduces each
component to the basic lemma. Item 6, the extension lemma, is done too
(2026-10-29), with the `RingedLattice` interface it needs. Remaining:

7. Modules wait. First concrete example after the affine sheaf and the
   invertibility support (step 4): the doubled-origin line, its lattice and
   sheaf from compatible pairs as in the note.

Note: `Gluing.Fr.Ks.w-power` opens `M` once: the checker represents the
recursive call of `power` at `suc M` as a stuck split, compared against
`P.power h M` by opening the scrutinee. Harmless (0.00 s).

Pointwise uniqueness in `ZariskiUniversal` is enough (funext + propositional
laws recover equality of lattice maps); no contractibility packaging.

## Functor of points: autonomous development, first checkpoint (2026-10-29)

Scope: full faithfulness of X |-> (B |-> Hom_k(Spec B, X)), on **all**
k-algebras with carriers in U l. The test object type and natural
transformations may live in U (l+1). This does not use the small category
of finitely presented algebras as a substitute for all affine tests.
The essential-image characterisation of scheme-valued functors is later.
The user has authorised continuing autonomously: write the precise informal
argument, review it, and formalise it. No new confirmation is needed for
routine steps in this scope.

Informal argument, written before the code: `doc/functor-of-points.tex`.
Evaluate a natural transformation at affine chart maps, use naturality on
affine probes to get agreement on chart overlaps, then glue. To show that
the resulting map induces the transformation, pull the chart cover back
to each affine test and refine by basic affine opens. Separation proves
the equation. Independence of a merely given atlas is proved before
eliminating it: the type of a map inducing the transformation is a
proposition. This proof needs a general finite-cover descent interface and
finite affine refinements of compact opens. The target can in fact be any
locally ringed lattice; only the source needs the qcqs atlas.

Checked supporting interfaces (14 new modules):

- `LatticeCover`: finite covers detect inequalities and equalities.
- `LatticeDescent`: p(u) = join_i p_i(u) glues inverse-image lattice maps;
  p(u) meet e_i = p_i(u), and uniqueness. The construction of image is
  opaque after its laws and cover equation.
- `FiniteLatticeFamilies`: concatenate finite families and compute their
  join. No ring structure on the lattice carrier is assumed.
- `SheafMaps`: compatible ring maps into a sheaf glue uniquely on a finite
  cover. `lift-matches` is the public restriction equation; lift is opaque.
- `MapAgreement`: agreement on e expressed in the ambient lattice, with
  equality of sections after restriction to any common smaller open.
  Finite-cover separation follows from lattice separation and the sheaf.
- `MapSeparation`: actual restriction to a source open, its lattice and
  section trace formulas, and equality detected by the restricted maps.
- `MapGluing`: compatible maps X|e_i -> Y glue; `Restricts.restricts` gives
  their actual restrictions and `unique` gives uniqueness. Ringed amalgams
  are contractible (`gluing`). Locality is proved by restricting the
  invertibility open to each e_i; local amalgams are contractible too
  (`Local.local-gluing`). Compatibility is stated explicitly on inverse
  images and section maps, without transporting a slice record.
- `SliceMap`: restrict a morphism to an inverse-image open, with the
  factorisation triangle, uniqueness, and locality.
- `SliceNested`: (X|e)|u is isomorphic to X|u for u <= e.
- `SliceIso`: an isomorphism restricts to an isomorphism on inverse-image
  opens. Section maps are the original bijection followed by restriction
  between equal opens.
- `AffineTransport`: affineness transfers across an isomorphism, by
  composition and AffineCriterion.
- `AffineBasis`: a compact open of an affine X merely has a finite affine
  cover. Lift it to Zar(Gamma X), present it by basic opens, and use
  SliceIso, SpecBasicOpen and AffineTransport.
- `AffineCoverJoin`: finite joins of opens with finite affine covers have
  finite affine covers, also under truncation.
- `AffineRefinement.refined`: every compact open of a qcqs scheme merely
  has a finite affine cover. Refine u meet e_i inside each affine atlas
  member; use SliceNested to forget the outer slice, then flatten.

All empty-cover cases are included. No existing proof or shared dependency
was changed: only All.seg imports and these new files. First full check:
`./segc sag/qcqs all`: 114 modules, 0 failed, 3.96 s. Each new declaration
was inspected with --opened, at most 25 distinct definitions and 0.01 s
in the inspected runs. One repair: MapGluing.matches originally unfolded
SheafMaps' amalgam construction. Adding lift-at / lift-matches beside lift
and making lift opaque removes that opening. Remaining slice-record field
comparisons are precisely the concrete restriction and identity-map steps;
AffineBasis also pays the existing transparent-Zariski-lattice comparison.
No fraction construction or truncation eliminator opens in gluing clients.
The inspected openings are recorded in `descent.opens` (428 entries).
The full `seg All.seg --opens descent.opens` check passes, with 4,985
declarations, zero failures, and no opening beyond the recorded lists.

Not yet formalised: full faithfulness itself. Next steps, in order:

1. Morphism identity laws and the two composition equations for Iso.Invert;
   its inverse map and bijectivity exist, but clients need the equations.
   Also record compatibility of SliceNested with inclusions.
2. A category-free large-test interface initially: points of X at a small
   ring B, precomposition by Spec of a ring map, and natural families.
   Prove the identity/composition laws for Spec as equality of local maps.
   Start with absolute morphisms; obtain the k-relative statement by the
   commuting structure-map condition.
3. Affine evaluation: a natural family on Spec A is determined by its value
   on the identity. SpecUniversal and Global identify every affine probe
   with Spec of its ring map. Keep level l+1 for the natural-family type.
4. Using an actual affine atlas, construct the local chart values, show
   compatibility via AffineRefinement and MapSeparation, then apply
   MapGluing. Check the induced transformation on every affine test.
5. Prove uniqueness first, eliminate mere existence of an atlas into the
   proposition of maps inducing the given transformation, and expose the
   equivalence of sets. Then impose the k-condition.

The mathematical note's final section distinguishes these checked
interfaces from the remaining theorem. It must continue to do so until
both inverse laws have checked.

### Relative comparison: precise reduction (informal proof first)

To pass from all-ring full faithfulness to the k-algebra statement, do not
merely take a fibre of the all-ring natural-transformation type: the test
category changes. For a base test K and a test ring B, a point p : Spec B -> X
has a unique lift (iota : K -> B, e : s_X p = Spec iota). AffineTests'
map equivalence gives this lift and proves its uniqueness. Thus
Sigma iota. PointOver(B,iota) is equivalent to the ordinary point set.
Reindexing a lifted point along h : B -> C uses the algebra structure
h iota; uniqueness compares this with the canonical lift of its ordinary
reindexing. Apply a relative natural transformation to the lift and forget
its base equation. This yields an all-ring natural transformation. The
absolute theorem recovers f, and its base compatibility is detected on
affine probes from the output base equations. Finally, any relative point
is the canonical lift of its ordinary point; this gives the relative
induced-recover law. Relative faithfulness follows by taking canonical
lifts of all ordinary probes, so gives the other inverse law. The same
argument is added to doc/functor-of-points.tex before formalising it.

## Functor of points: full faithfulness checked (2026-10-29)

The first-checkpoint Next 1--5 are now done for both absolute and relative
morphisms. The relative test category is **all** small k-algebras.

Public results:

- `PointsUniversal[l].Over[X,Y,qcqs].equivalence`: induced is an equivalence
  Hom(X,Y) -> Nat(h_X,h_Y), on all small commutative rings.
- `RelativeUniversal[l].Over[K,X,Y,sx,sy,qcqs].equivalence`: induced is an
  equivalence Hom_K(X,Y) -> Nat(h_X^K,h_Y^K), on all small K-algebras.
- Only X needs to be qcqs; Y may be any locally ringed lattice.
- `induced-recover` and `recover-induced` are both checked equalities.
  `recover` uses a merely existing atlas, eliminated only after showing
  its type of solutions is a proposition. The elimination is at l+1.
- Hom and relative Hom are sets in U l; natural transformation types are
  sets in U (l+1). There is no resizing and no restriction to f.p. tests.

19 new modules in this checkpoint:

1. `MapLaws`: both unit laws and both equations for Iso.Invert's inverse,
   as equalities of maps. The second inverse law uses injectivity of pi#,
   naturality and proof-independence of restriction.
2. `Spaces`: one packaging of a lattice with its existing locally ringed
   structure, with local maps in geometric order. Hom, set, ext, identity,
   composition, associativity, inverses and cancellation. No univalence
   of this object type is asserted.
3. `AffineTests`: all small rings with set carriers; Spec of their maps,
   the identity and composition laws, and every affine morphism as Spec
   of a unique ring map (MapsEquivalence).
4. `FunctorPoints`: ordinary point sets, reindexing and its laws, natural
   families, their extensionality and sethood, induced transformations,
   composition of natural families, and naturality for arbitrary affine
   morphisms via MapsEquivalence.
5. `AffineEvaluation`: Nat(h_(Spec A),h_Y) equivalent to Hom(Spec A,Y),
   by evaluation at identity, on this large test category.
6. `AffineSource`: the same theorem for any affine source, transferred
   along its canonical isomorphism. canonical-iso is the public witness;
   canonical is opaque after it.
7. `OpenMaps`: geometric open inclusions, inclusions X|u -> X|e for u<=e,
   their triangle and the lattice and section traces of restriction.
   These supply the inclusion comparisons needed here without identifying
   nested slices along a path of records.
8. `SliceQcqs`: every compact open of a qcqs scheme is qcqs, using the
   affine refinement and inverse of the nested-slice isomorphism.
9. `ProbeSeparation`: equality detected on all affine probes out of a
   qcqs source, and faithfulness of induced natural transformations.
10. `OpenAgreement`: equality on the overlap becomes MapGluing's exact
    inverse-image and section agreement conditions.
11. `AtlasMap`: evaluate a natural family on affine charts, compare on
    overlap probes, and glue the chart maps. Gives the actual restriction
    equations and the equation on all chart probes.
12. `OpenPullback`: the geometric square obtained by restricting a map to
    an inverse-image open, using SliceMap.triangle.
13. `TopOpen`: X|top -> X is an isomorphism, including its section maps.
14. `AffineQcqs`: an affine space is qcqs; in particular each affine test
    is qcqs, by AffineCriterion at the identity.
15. `AtlasMapPoints`: the map from AtlasMap induces the given family on
    every affine point. Pull back the chart cover; compare on affine
    probes into each inverse image; use separation twice.
16. `PointsUniversal`: solutions form a proposition by faithfulness and
    sethood of Nat. Mere existence of an atlas gives its solution; the
    two inverse laws give the absolute equivalence.
17. `BasePoints`: all K-algebra tests as (test ring, structure map), their
    morphisms and relative points, with reindexing laws. For a fixed ring,
    lifts of an ordinary point form a proposition. Total relative points
    and ordinary points are equivalent (At.forget-equivalence).
18. `RelativeFamilies`: relative natural transformations and induced maps,
    and extension to ordinary rings using canonical lifts. Shows ordinary
    naturality, compatibility with the base point, and recovery of the
    underlying value on any relative point. Both map and Nat types are sets.
19. `RelativeUniversal`: recover the absolute map of the extended family;
    affine probes prove its base condition. Relative point extensionality
    gives induced-recover, and relative faithfulness gives recover-induced.

Informal proof and review: `doc/functor-of-points.tex`, including a new
section explaining why the relative statement needs more than taking a
fibre of the all-ring Nat type (the test category changes). The final
section now states what is checked, including both theorem names.

Checking after these changes: `./segc sag/qcqs all` gives 133 modules,
0 failed, 3.98 s. `points.opens` records 625 reviewed declarations;
`seg All.seg --opens points.opens` checks 5,610 declarations, 0 failed,
and nothing beyond the recorded lists (4.83 s in that run).

Opening repairs, following WRITING.md:

- AffineTests' first composition proof took 6.2 s and opened the extension
  and truncation construction while comparing differently named views.
  `underlying-map`, `composite-view`, and `second-view` state the common
  points explicitly; Map.morphism is opaque after its interface. The
  entire AffineTests file then checks in about 0.26 s.
- ProbeSeparation initially compared the old affine criterion witness
  with the packaged canonical map, opening the Spec construction while
  instantiating an inverse. AffineSource now exposes canonical-iso and
  makes canonical opaque. That inverse-module instance now opens 7 names
  in 0.00 s instead of 54 names in 0.14 s.
- The largest remaining distinct count is 35, in AffineTests.Identity's
  by-definition global component comparison. Map.component still opens
  spec/structure views repeatedly (about 0.13 s in the audit); no extension
  construction or truncation eliminator is opened there. This is a local
  interface observation, not a reason to change shared code.
- Algebra tests use the ordinary Sigma (B, iota) with named accessors.
  This makes the total-point argument a reordering of Sigma types, without
  requiring an eta law for an anonymous algebra record.

No shared dependencies or core files were changed. All earlier examples
continue to pass. The new work and the earlier first checkpoint remain
uncommitted.

Next comparison milestone: essential image, not full faithfulness.
Define open subfunctors and finite open affine atlases, formulate overlap
quasi-compactness, and prove reconstruction by gluing with transition
isomorphisms and cocycle laws. Write and review that mathematical proof
before coding it. Packaging the geometric objects as a univalent category
is a separate interface theorem; the pairwise Hom--Nat equivalences above
are already checked and do not depend on that packaging.

## Essential image: compact-open foundations (2026-10-29)

The user authorised autonomous continuation after full faithfulness. No
fresh session was required to begin. Informal statement and reviewed proof,
written before the code: `doc/functorial-schemes.tex` (compiled PDF beside it).
It follows zeuner1 Sections 4--5 and zeuner3 Sections 5--6, with a direct
small finite-tuple reconstruction rather than constructing a large locally
ringed lattice and then implementing universe lifts. References include
Coquand--Lombardi--Schuster, Spectral schemes as ringed lattices.

Precise statement to prove: a small-set-valued functor on **all** small
commutative rings is a Zariski sheaf with a merely given finite affine
compact-open atlas iff it is merely naturally equivalent to h_X for a
small qcqs locally ringed lattice X. Relative version: totalise a functor
on k-algebras by Sigma(iota:k->B).F(B,iota), apply absolute reconstruction,
and recover the structure map to Spec k by full faithfulness.

Review points fixed before implementation:

- Compact opens are natural maps F -> Zar, not a collection of arbitrary
  subobjects modulo isomorphism. Their realisation is Sigma(x:F(B)).U(x)=top.
- Requiring an atlas of these compact opens already ensures compactness
  of every affine pullback, hence of overlaps. Do not require affine
  overlaps (that would be a stronger condition) or add a redundant extra
  quasi-separatedness assumption.
- CompOpen(F) initially lives in U(l+1), even though each Zar(B) is small.
  Do not silently resize it. The proposed small reconstruction uses
  compatible tuples in finitely many chart lattices, and rings of tuples.
- Transition isomorphisms require domain equations on triple overlaps
  before their cocycle equation is stated. Equality of chart maps into F
  supplies these through full faithfulness and monicity of the inclusions.
- An actual atlas yields an actual reconstruction. For a merely given
  atlas, conclude mere existence of a representing small scheme. An
  untruncated canonical geometric representative requires the separate
  univalence theorem for the category of spaces.
- Empty covers are included. The empty scheme's value on the zero ring
  is a singleton, so it must not be confused with the everywhere-empty
  functor. Locality demands F(0) contractible.

Checked: 23 new modules; existing full faithfulness and examples unchanged.

1. TestFunctors: arbitrary small-set-valued functors on all small test
   rings, natural transformations, their extensionality and sethood,
   composition and affine representables. Existing FunctorPoints are
   instances, and their natural families coincide with this Sigma form
   by definition. No existing full-faithfulness proof was refactored.
2. TestYoneda: evaluation Nat(h_A,F) equivalent to F(A) for arbitrary F;
   the equivalence is at l+1. Also Nat(h_A,h_B) equivalent to Hom(B,A).
3. TestEquivalences: componentwise equivalences have natural inverses;
   inverse equations and composition, without equality of functor records.
4. ZariskiFunctor: h_* is the unique lattice map D(a) |-> D(h(a)); identity
   and composition from uniqueness. spec-lattice identifies the geometric
   inverse image with this lattice map. Public unique and on-D interfaces;
   lattice-map is opaque after them.
5. CompactOpens: Nat(F,Zar) as a bounded distributive lattice in U(l+1),
   pointwise operations, pullback along natural maps, and the affine
   Yoneda equivalence with Zar(A).
6. OpenRealisation: |U| as a set functor, its injective inclusion, and
   unique natural lifting of maps whose values satisfy membership.
7. CompactPullback: along x in F(A), the classifier is the Yoneda extension
   of U_A(x); membership at h is equivalent to h_*(U_A(x))=top.
8. GeometricOpens: e |-> (p |-> p*(e)), preserving lattice operations;
   realisation naturally equivalent to h_(X|e), from factor-cut and restore.
9. TestSheaves: the finite basic localisation diagram, with overlap rings
   B[1/(a_i a_j)] and restriction maps rho; compatible families, contractible
   amalgams, and IsSheaf as a proposition. Includes empty covers.
10. RepresentableSheaf: every h_A is a sheaf, via the earlier basic ring
    gluing and separation theorem. Glue values into B[1/1], prove they
    form a ring map by separation, then use Global.back to land in B.
11. ZariskiSeparated: Zar is separated on finite basic covers. Use
    SpecBasicOpen's isomorphism and factor-cut to turn equality after
    localisation into equality after meeting with D(a_i), then LatticeCover.
12. OpenSheaf: realisations of compact opens of sheaves are sheaves.
    Forget membership, glue, and use Zar separation to prove membership.
13. WholeRealisation: realisation of top naturally equivalent to F.
14. SheafTransfer: sheafhood transfers across a natural equivalence.
15. FunctorialQcqs: intrinsic IsAffine, finite affine compact-open covers,
    IsQcqs (a proposition), and representables as functorial qcqs schemes.
    Affine functors are sheaves by transfer under truncation.
16. GeometricEquivalence: isomorphic spaces give naturally equivalent
    geometric functors, using the geometric inverse equations.
17. AffineFunctor: h_(Spec A) naturally equivalent to algebraic h_A, and
    every geometric affine space gives an affine functor.
18. GeometricAtlas: a geometric qcqs atlas gives a functorial compact-open
    affine atlas, using GeometricOpens and AffineFunctor. This proves the
    atlas statement; it does not yet prove sheafhood for general h_X.
19. ZariskiUnits: D(b)=top iff b is a unit, via Bridge at powers of 1 and
    reflection of units along the bijective inclusion B -> B[1/1].
20. BasicAffineFunctor: |D(a)| naturally equivalent to h_(A[1/a]), using
    localisation's universal property and ZariskiUnits. Exposes affine.
21. CompactAffineCover: every compact open of h_A is a functorial qcqs
    scheme. Present U_A(1) by D(a_i), pull these back to |U|, and prove
    each realisation equivalent to |D(a_i)| by forgetting the redundant
    membership proof. The atlas merely exists; its construction is
    eliminated into HasAtlas at l+1. Sheafhood comes from OpenSheaf.
22. FiniteLatticeGlue: the small lattice of compatible tuples v_i for
    arbitrary comparison maps L_i -> M_ij <- L_j; projections and its
    universal property. No cocycle hypothesis is needed for this limit.
23. FiniteRingGlue: corresponding small ring of compatible tuples, its
    projections and universal property. Units are detected coordinatewise;
    inverse compatibility is uniqueness of inverses on each overlap.

Checks: `./segc sag/qcqs all`: 156 modules, 0 failed, 4.38 s. All new
702 declarations were inspected with --opened, maximum 42 distinct
names and 0.05 s per declaration in that run. `essential-image.opens`
records these openings; `seg All.seg --opens essential-image.opens`
checks 6,312 declarations, zero failures, and nothing beyond the lists
(5.12 s in that run). No new axiom, no shared dependency changes.
Everything since the previous qcqs checkpoint is still uncommitted.

Opening repair: composition in ZariskiFunctor initially opened the
radical-transitivity proof and Trunc.induction while comparing the
constructed map with its composite. Exposing unique at the public
lattice-map type, stating hmap-compose explicitly, and making lattice-map
opaque fixes it: on-D now opens 9 names and composition 4, with no
radical proof or truncation eliminator. The remaining maximum is the
comparison between SpecBasicOpen's factorisation and ZariskiFunctor's
map in ZariskiSeparated.cut-image (42 names, 0.05 s): it opens the
slice/Spec/Zariski interface records, not their existence proofs.

### Essential-image continuation: historical checklist (superseded below)

Do not claim the essential-image theorem or general h_X sheafhood yet.

1. Finite geometric gluing using the two new limits. Given spaces X_i and
   local maps Y_ij -> X_i, Y_ij -> X_j, form the FiniteLatticeGlue lattice
   and the FiniteRingGlue section rings, with the second overlap leg
   restricted along the equality of overlap opens. Generalise GlueAlong's
   componentwise restrictions, sheaf proof, and invertibility support.
   Prove the resulting structure and projection maps. Then impose actual
   open-transition data with domain and cocycle laws to prove the chart
   isomorphisms and finite-cover equation. Follow Section 5 of the note;
   do not impose affine overlaps. The two finite limits are already checked.
2. Compact-cover descent of natural maps into a sheaf (Section 6 of the
   note, zeuner1 Lemma 4.26). Use a finite basic refinement of U_i(x) on
   each test ring. Prove uniqueness first; eliminate presentations into
   that proposition; use the characterising equation to prove naturality.
3. Connect geometric finite-cover descent to TestSheaves' localisation
   diagram to prove IsSheaf(h_X) for arbitrary geometric X. BasicOpen's
   chart isomorphisms and the Spec/restriction triangles identify the
   Cech diagram; use the geometric gluing theorem for its amalgams.
   HasAtlas(h_X) is already GeometricAtlas.has-atlas for qcqs X.
4. From a functorial affine atlas, obtain the transition isomorphisms on
   compact-open overlaps. CompactAffineCover makes these overlaps qcqs;
   GeometricOpens, affine Yoneda and full faithfulness recover the maps
   and their inverse/domain/cocycle equations. Glue and identify F with
   h_X by compact-cover descent in both directions.
5. Conclude mere representability from a mere atlas. Then totalise
   relative functors as Sigma(iota:k->B).F(B,iota) and recover the base
   map by full faithfulness, as in Section 7 of the note.
6. Separate later result: univalence of geometric objects/category and
   categorical equivalence. It is not implied merely by Hom--Nat
   equivalences and mere representability without that packaging.

## Essential image: finite gluing and compact descent checked (2026-10-29)

This checkpoint supersedes the preceding continuation checklist. The
mathematical presentation is `unit/doc/functorial-schemes.tex` (seven-page
PDF), mathematics first and implementation correspondence only at the
end. No claim of the full essential-image theorem is made yet.

### Precise finite gluing hypotheses and theorem

For spaces X_i and compact opens d_ij in X_i, write Y_ij=X_j|d_ji.
A local map h_ij:Y_ij->X_i gives a bounded lattice map
r_ij:L_i -> L_j|d_ji; let t_ij be its underlying function into L_j.
Use the following domain-sensitive laws:

    t_ii(u) = u,
    t_jk(t_ij(u)) = d_kj /\ t_ik(u).

In particular t_ji(t_ij(u))=d_ij /\ u. The diagonal top law d_ii=top
follows from identity and preservation of top by r_ii. These laws say
where triple compositions are defined, as well as what they do there.
The corresponding ring maps c_ij,u:O_i(u)->O_j(t_ij(u)) satisfy:

    c_ii,u(s)|u = s,
    c_jk,t_ij(u)(c_ij,u(s)) = c_ik,u(s)|t_jk(t_ij(u)).

The second equation is expressed as compatibility of the transported
tuple, with the restrictions and equal domains in its type. These are
hypotheses of the gluing theorem, not added axioms. In particular the
extraction of these hypotheses from a functorial atlas remains to do.

Checked files (informal proofs at their heads):

- FiniteRingedGlue: for any finite diagram of local maps, sections on a
  compatible tuple of opens form FiniteRingGlue's ring. Restriction is
  componentwise; naturality of the legs proves compatibility. Sheaf
  gluing is coordinatewise; separation on each overlap proves that the
  glued coordinates agree. Includes empty atlases and empty covers.
- FiniteLocalGlue: D(s) is the tuple of D_i(s_i). Locality of the legs
  and InvOpen.Restrict prove compatibility. FiniteRingGlue's unit
  criterion proves that it is the invertibility open; support laws hold
  coordinatewise. Each component has a local projection map into the
  glued space. OverlapAgreement proves that the two composites from
  each Y_ij into the glued space are equal (matching on opens and rings).
- FiniteTransitionLattice: extend u in chart i to (t_ij(u))_j. The
  cocycle law is exactly its compatibility. Chart e_i is extension of
  top, with j-coordinate d_ji and i-coordinate top. The charts cover.
  Below e_i, matching says t_ij(v_i)=v_j /\ d_ji=v_j. Projection and
  extension are inverse, proving the lattice chart theorem.
- FiniteTransitionGlue: on v<=e_i a section tuple is determined by its
  i-th coordinate. Matching gives every other coordinate by transport
  and restriction between equal opens. Conversely transport a section
  over v_i to the tuple on extension_i(v_i), then restrict to the equal
  open v. Section identity proves it projects back to the given section.
  Thus section projections are bijective. SliceUniversal factors the
  projection X_i->glued through e_i; its lattice and section maps are
  bijective, so X_i is isomorphic to glued|e_i. AffineInputs packages
  affine charts into an actual affine cover and proves qcqs. Affineness
  of pairwise overlaps is never assumed.

FiniteLatticeGlue also exposes coordinatewise order and preservation of
finite joins, needed to send covers to component and overlap covers.

### Geometric functors are sheaves

- SpaceGluing: the existing geometric finite-cover gluing theorem with
  hypotheses and conclusions directly in Spaces.Hom. Maps on X|e_i
  agreeing on intersections have contractible amalgams. OpenAgreement
  supplies MapGluing's component hypotheses; MapSeparation supplies
  uniqueness. No affine or qcqs source hypothesis is used.
- OpenMonic: an open inclusion is a monomorphism, by SliceUniversal.cancel.
- BasicGeometry: j_g:Spec(B[1/g])->Spec(B)|Dg, its isomorphism and
  factor-cut triangle. For Dh<=Dg, the square between j_h,j_g, Spec(rho)
  and the open inclusion commutes. After composing into Spec B this is
  Spec's composition law and rho-on; OpenMonic cancels that inclusion.
  Value and Pull.trace compare maps on the localised affine with their
  restrictions on basic opens.
- GeometricSheaf: compatible points on the standard basic localisation
  diagram transfer via inverse j_i to maps on D(a_i). Pull.trace and
  cancellation of j_(a_i a_j) prove agreement on D(a_i a_j); transport
  along D(a_i a_j)=D(a_i)/\D(a_j) gives intersection agreement. SpaceGluing
  gives the point on Spec B; its chart equations give the matching laws.
  Uniqueness follows after cancelling each j_i and using geometric
  uniqueness. Thus IsSheaf(h_X) holds for EVERY locally ringed lattice X.
- GeometricAtlas.qcqs now combines this with its already checked atlas:
  every geometric qcqs scheme is a functorial qcqs scheme. This completes
  the necessary direction of the essential-image theorem.

Spaces.InvertMap gains cancel-forward (precomposition by an isomorphism
detects equality), by associativity and its inverse law. AffineTests
names the localised test once as localised B g; the recent localisation
and geometric interfaces and TestSheaves use this same test.

### Compact-cover descent and local-to-global equivalence

- LocalisationTests: Dg<=u iff beta_g*(u)=top. The forward direction uses
  the unit beta_g(g); the reverse uses ZariskiSeparated's intersection
  lemma. The localisation base-change square B_g->C_(h g) comes from
  the universal property alone; Functor.equation states its image under
  any test functor. No fraction construction is analysed.
- CompactMembership: local membership from Dg<=U_B(x), and its general
  version for a ring map sending Dg to top, by naturality of U.
- TestSheaves.SheafProperties: separation follows from uniqueness of
  amalgams of the restrictions.
- CompactCoverDescent: for any F, sheaf H, finite compact-open cover U_i,
  and compatible alpha_i:|U_i|->H, the type of natural extensions is
  contractible (Glue.universal). F need not be a sheaf.

  A candidate y at x in F(B) fits when for every h:B->C and every i
  with F(h)x in U_i, H(h)y equals alpha_i(F(h)x). First prove candidates
  form a proposition: a merely existing tagged basic refinement of
  U_i(x) detects equality by sheaf separation. For existence, take a
  refinement, apply alpha to the localised points, and glue. Overlaps
  agree by naturality and compatibility. To prove fitting after h,
  use the pulled-back cover h(a_k) and the localisation base-change
  square; both restrictions become local alpha values at the same point.
  Separation proves fitting. Eliminate the mere refinement into the
  proposition of candidates. Naturality follows from stability of
  fitting under change of B. The fitting equation at identity gives
  the local equation. Any other natural extension fits, hence is equal.
  candidate is opaque after result and fits are exposed: no client
  opens the refinement selection or sheaf construction.
- CompactCoverSeparation: natural maps into a sheaf are equal if they
  agree on a finite compact-open cover, by the uniqueness above.
- LocalFunctorIso: given finite compact-open covers of sheaves F,H and
  natural equivalences between their chart realisations, compatible in
  both directions, glue their maps and inverses by CompactCoverDescent.
  Each composite restricts to identity by the local inverse equations;
  CompactCoverSeparation proves both global inverse equations. Exposes
  a natural equivalence. This is the final local-to-global interface
  needed after geometric atlas reconstruction.

### Correspondence with reading: repairs made before accepting the check

1. Affineness of a glued chart initially overran the 10 s declaration
   limit. Using Iso.Invert at the slice's own ringed type, then stating
   the affine criterion at that same slice before Qcqs.AffineOpen, makes
   the comparison immediate. No proof or mathematical theorem changed.
2. A chart map initially opened the glued space 18,313 times and opened
   funext's construction. Naming the slice via OpenMaps.At[G.space,e]
   and its factorisation at G.space's own lattice/structure removes the
   duplicated comparison; morphism now opens 16 names in 0.00 s.
3. Packaging BasicGeometry.j and its triangle directly compared every
   lattice/sheaf law, including quotient induction and funext's proof.
   Splitting the ringed and local components only moved that comparison.
   SpacePaths is the mathematical solution: transport morphisms and
   diagrams along equalities of spaces, preserving composition and
   isomorphisms by path induction. Check the basic-open triangle at its
   defining spaces, then change the WHOLE diagram. The source/target
   equalities each open only 3 names, and no downstream proof rechecks
   lattice or sheaf laws. All BasicGeometry declarations now open at
   most 29 names. This illustrates why equal presentations should be
   related once, rather than compared repeatedly by computation.
4. Module-name collisions were handled locally (e.g. AtChart,
   AffineInputs); they do not enter the mathematical note. The module
   system is unchanged.

Validation: 170 modules, zero failures. The full independent
`seg All.seg --opens essential-image.opens` checks 6,991 declarations,
zero failures (6.76 s in that run). This historical 1,493-entry audit was
subsequently refreshed to record the shared AffineTests.localised
constructor in existing basic-cover clients; the complete audit at the
following checkpoint supersedes it. The 20 refreshed/extended modules have 920 audited
entries; the 14 new source modules have 764 checked declarations in
1,300 lines. Each new declaration takes at most 0.07 s and opens at
most 38 distinct names in the isolated audit run. No new axiom, no shared
dependency changes, and no edits to core or the category development.
Everything since the previous qcqs checkpoint remains uncommitted.

### Coherent atlas extraction: historical checklist (superseded below)

Do not claim the sufficient direction or the complete essential-image
theorem yet. The following are genuine remaining arguments.

1. Realisations of pullbacks and intersections: natural equivalences
   identify |U_i /\ U_j| with the compact-open subfunctor pulled back
   along either affine chart. On h_A this compact open is classified
   by its value at identity (TestYoneda/CompactPullback). Relate it to
   GeometricOpens on Spec A, using AffineFunctor. This produces geometric
   overlap representations Spec(A_i)|d_ij, with compatible inclusion
   maps into the common functor F.
2. Recover transition isomorphisms by full faithfulness on these qcqs
   overlaps (SliceQcqs). Their composites agree because they describe
   the same point in F. Prove the domain equations on triple overlaps
   BEFORE applying faithfulness to the section cocycle. In particular
   verify the precise FiniteTransitionLattice and FiniteTransitionGlue
   hypotheses above; they have not been extracted automatically from an
   arbitrary chart equivalence yet. Do not assume affine overlaps.
3. Apply FiniteTransitionGlue. Its chart isomorphisms, GeometricOpens,
   and the original chart equivalences give chartwise equivalences
   between F and the geometric functor of the resulting space. Check
   compatibility in both directions, using the recovered transitions
   and FiniteLocalGlue.OverlapAgreement. LocalFunctorIso then gives the
   global natural equivalence; GeometricSheaf supplies sheafhood of
   the geometric functor and AffineInputs supplies geometric qcqs.
4. Untruncate only into mere representability. A functorial affine atlas
   and its affine witnesses merely exist; use finite choice and the
   proposition of mere representations, not a choice of presentations
   for each algebra or a presumed univalence theorem for spaces.
5. Relative version: totalise F as Sigma(iota:k->B).F(B,iota), apply the
   absolute result, recover X->Spec k by full faithfulness, and take
   fibres. Follow Section 7 of the note.
6. A literal equivalence of univalent categories additionally needs the
   geometric category's packaging and univalence; neither is asserted
   merely from full faithfulness and mere essential surjectivity.

## Essential image: overlap representations and domains checked (2026-10-29)

Continued beyond the finite-gluing/descent checkpoint. The full tree now
has 179 modules, zero failures (5.68 s). The independent full
`seg All.seg --opens essential-image.opens` checks 7,232 declarations,
zero failures, with no openings outside its 1,734 lists (7.22 s).
The 23 new files of this continuation contain 1,004 declarations and
1,759 lines. New declarations take at most 0.07 s; the maximum number
of distinct openings is now 45, in AtlasDomains.first (the comparison
between its slice type and the recovered transition's source type).

### Overlap representation: mathematics first

For an actual chart e:h_A ~= |U| of F, compose the inverse affine
comparison h_(Spec A) ~= h_A with e and the inclusion into F. This is
its geometric chart-inclusion transformation. It is injective on affine
points: its lift to |U| is an equivalence and |U|->F has proposition
fibres. On a qcqs source, equality of maps into this affine chart is
therefore detected after their inclusion into F, using affine probes.

For a second compact open V, pull V back first to |U| and then along e.
The result W is a compact open of h_A; write d=W_A(1). Naturality gives
h_*(d)=W_B(h). The affine comparison takes h to Spec h, so this equation
identifies |W| with the realisation of the geometric classifier of d.
Thus |W| is represented by (Spec A)|d, a qcqs space. Forgetting the two
membership proofs identifies |W| with |U /\ V|. This comparison keeps
the underlying F-point and identifies the open inclusion with the
restriction of the geometric chart-inclusion transformation.

Using two charts gives geometric representations of |U /\ V| and
|V /\ U|. Swapping the intersection preserves the F-point. Compose one
representation with the inverse of the other. Full faithfulness recovers
a transition map and the inverse natural equivalence recovers its
inverse map. Equality on all affine points gives both inverse equations;
Compose.Inverse gives isomorphism in the concrete ringed-lattice sense.
The transition still preserves the point of F.

For any third compact open W, let d_AW and d_BW be its extents in the
two affine charts. On every affine probe p of the first overlap, the
inverse images of cut_B(d_BW) under the transition and of cut_A(d_AW)
are the W-values of the same F-point. Hence they are equal. Affine
probes detect compact opens of qcqs spaces: choose an actual affine
atlas, test with the inverse canonical affine isomorphisms, cancel their
bijective lattice maps, and apply LatticeCover. Mere existence of the
atlas is eliminated only into equality. This proves the DOMAIN equation
before the cocycle is stated on those triple domains.

### Checked interfaces

- RealisationTransfer: a natural equivalence preserving and reflecting
  membership restricts to an equivalence of realisations. forward-point
  records its underlying point. It is opaque after that equation.
- OpenIntersections: realising the pullback of V to |U| gives |U /\ V|.
  The inverse splits a meet equal to top into its two top equations.
  forward-point records the same F-point; the equivalence is then opaque.
- AffineOpenRealisation: for every compact open u of h_A, equivalence
  represents |u| by AR.space=(Spec A)|u_A(1), with AR.qcqs and trace for
  its inclusion into h_(Spec A). Does not assume the open is affine.
- AtlasOverlap: chart-equivalence, chart-inclusion and generic point;
  injectivity on affine points and detection of equality of maps from
  qcqs sources. With[V] gives the overlap's geometric representation
  (AR.space, AR.qcqs, equivalence), extent at the generic chart point,
  classifier on every affine probe, and trace of the inclusion into F.
- OpenSymmetry: swap the intersection realisations, keeping the F-point.
- GeometricRecovery: recover a geometric isomorphism from a natural
  equivalence of the geometric functors of two qcqs spaces, with its
  inverse and both equations. The recovered maps are opaque once their
  equations on probes are exposed. Neither space needs to be affine.
- GeometricOpenSeparation: affine probes detect equality of compact
  opens of any qcqs space, by the affine-atlas argument above.
- AtlasTransition: the natural equivalence of overlap functors, recovered
  transition G.forward and isomorphism G.iso. Point.overlap-equation
  preserves the F-point, and Point.chart-equation is the usual square
  with both geometric chart inclusions.
- AtlasDomains: for that transition and ANY third compact open W,
  equation states theta*(cut_B d_BW)=cut_A d_AW. Thus triple-overlap
  domains agree. The proof uses AtlasOverlap.classifier, the transition
  chart-equation, and GeometricOpenSeparation.

AffineFunctor.Spectrum.map-at now states the value of the forward
natural equivalence, and the equivalence is opaque immediately afterward.
The source-level inverse must not compute the inverse in its proof of
bijectivity. Before this lock, AtlasOverlap.trace opened Global.iso,
Global.back, and polynomial/section representations; after the lock it
uses only the inverse law. Likewise the realisation and overlap
comparisons are opaque after their forward-point/trace equations.
The largest AtlasOverlap declarations now open 36 names (formerly 92),
and AtlasTransition at most 39 (formerly 64). No existence construction
or proof of equivalence is recomputed in the clients.

The mathematical note is updated, including the order of the domain
argument before the cocycle argument. Implementation details occur only
at the end. No new axiom or shared dependency change; no edits to core
or sag/categories. Everything remains uncommitted.

### Previous continuation: cocycles, reconstruction, truncation (completed below)

1. Cocycle on the identified domains. For three affine charts, restrict
   the transitions using AtlasDomains. On every affine probe the two
   composites into the final affine chart give the same F-point, by
   AtlasTransition.Point.chart-equation and associativity. Use the
   final chart's AtlasOverlap.injective, then its Maps.equal on the qcqs
   triple overlap. This gives equality of actual local maps. Prove
   identity and inverse compatibility in the same way. Do not compare
   composites before identifying their domains.
2. Convert this geometric cocycle to the exact restriction-and-transport
   hypotheses of FiniteTransitionLattice and FiniteTransitionGlue.
   For h_ij:X_j|d_ji->X_i use the recovered transition followed by the
   chart inclusion. Its underlying t_ij satisfies the domain-sensitive
   lattice identity, and equality of maps on the triple domain gives
   SectionCocycle by MapAgreement.restrict-eq and res-comp. The identity
   map gives SectionIdentity. These specific hypotheses have NOT yet
   been verified for the extracted atlas data.
3. Apply FiniteTransitionGlue to these maps. Its chart isomorphisms,
   GeometricOpens, and the original affine chart equivalences identify
   the realisations of the chart covers of F and of h_X. Verify forward
   and inverse overlap compatibility using the extracted transition
   equations and FiniteLocalGlue.OverlapAgreement; LocalFunctorIso then
   gives F ~= h_X. GeometricSheaf gives sheafhood of h_X, AffineInputs
   gives the geometric qcqs proof. This is the sufficient direction.
4. The actual affine chart witnesses merely exist in FunctorialQcqs's
   atlas. Use finite choice and eliminate into MERE representability,
   not a chosen space and not a presumed univalence theorem for spaces.
5. Relative totalisation and categorical packaging remain as in the
   note. Neither is needed to state the absolute Hom--Nat comparison
   with mere essential surjectivity; literal equivalence of univalent
   categories additionally needs the geometric category's univalence.

Audit detail for continuation: `--opens` reports extra openings but can
still exit zero. The final audit explicitly checks that every OPENS line
says "nothing else opened" (1,734 of 1,734). Naming the localised test
centrally added AffineTests.localised as a by-definition opening in 19
existing basic-cover declarations; those exact entries were inspected
and recorded, with no other extra opening.


## Essential image: absolute reconstruction complete (2026-10-29)

Continued from the final overlap/domain checkpoint without changing core,
the category development, or any shared dependency implementation. The
informal restricted-cocycle proof and its review were written first in
`unit/doc/functorial-schemes.tex`; every new module also starts with its
informal argument. The note and its eight-page PDF now describe the
checked absolute theorem and the remaining relative/categorical boundary.

### Transition equations on their identified domains

Use the gluing indices `h_ij : X_j|d_ji -> X_i`. AtlasData packages these
maps from the recovered transitions. Their trace preserves the F-point;
the generic point belongs to its own chart, so `d_ii=top`. AtlasInverse
proves that a repeated transition is identity and that reversing the two
charts gives an inverse transition. Cancelling the final open inclusion
turns equality into the chart into equality in the overlap space itself.

For a triple, first put `q=t_jk(d_ji)`. AtlasDomains gives
`q=d_ki /\ d_kj`, so `q<=d_kj,d_ki`. OpenFactor restricts `h_jk` to
`X_k|q` and factors it through `X_j|d_ji`. AtlasCocycle compares
`h_ij` after this factor with `h_ik` after the inclusion into `X_k|d_ki`.
Their F-points agree on every affine probe by the transition traces and
factorisation triangles. The source is qcqs by SliceQcqs, so the final
chart's injectivity and Maps.equal give equality of these actual maps.
The domains have been identified before the composites are compared.

AtlasLaws takes inverse images of that equality. Monotonicity removes
the meet with q on the left; the domain equation and `t_ik(b)<=d_ki`
simplify the right. This is exactly
`t_jk(t_ij(b))=d_kj /\ t_ik(b)`. The diagonal gives `t_ii(b)=b`.
AtlasSections restricts the equality of maps to the common open
`w=t_jk(t_ij(b))`. The sharp-composite formula, OpenFactor.trace,
OpenMaps.Below.Pull.trace, Slice.res-inc and res-comp give precisely
FiniteTransitionGlue.SectionCocycle. The diagonal map equality gives
SectionIdentity. Neither law is left as an extra atlas hypothesis.

### Reconstruction, compatibility, and mere witnesses

AtlasReconstruction applies FiniteTransitionGlue to these extracted laws.
It exposes the glued space, its geometric chart realisations, their
natural equivalences with the affine input charts, and the classifier
identity `V_j(inclusion_i p)=U_j(point_i p)`. AffineInputs proves qcqs.

AtlasCompatibility proves both required directions. Equal F-points put
one chart point in the overlap by the original classifier. Factor that
point, identify its transition image using original chart injectivity,
and use FiniteLocalGlue.OverlapAgreement to get equal glued points.
Conversely equal glued points put the point in the overlap using the
reconstructed classifier. The same overlap square and reconstructed
chart injectivity identify its transition image; the transition trace
then gives equal F-points. AtlasRealisation applies LocalFunctorIso to
these two compatibility statements. Its result is `F ~= h_X`.

FiniteLargeChoice proves finite choice for witnesses in `U(l+1)` indexed
by the existing `Presentations[l].Fin n`. Instantiating AffineFinite at
`l+1` would instead change the finite index type, so it is not silently
used in place of this lemma. FunctorialTransfer pulls affine atlases and
sheafhood back across natural equivalences.

EssentialImage.Over[F] exposes:

- `Representation`: a small space X, its geometric qcqs proof, and
  `F ~= h_X`.
- `IsRepresentable`: the propositional truncation of Representation.
- `reconstruct : FunctorialQcqs.Over[F].IsQcqs -> IsRepresentable`.
  Finite choice supplies the affine witnesses merely; both their
  truncation and the atlas truncation are eliminated only into this
  proposition.
- `recognise : IsRepresentable -> FunctorialQcqs.Over[F].IsQcqs`, using
  GeometricAtlas and FunctorialTransfer.
- `equivalence`: the equivalence of these two propositions.

### Review and validation

The opening audit prompted two local repairs before acceptance.
OpenFactor.factor is opaque after its triangle, lattice equation and
section restriction equation. Its at-le accessor is stated at that
opaque map, so clients do not depend on computation of Back. The atlas
transition maps are likewise opaque after their equations. The diagonal
uses AtlasInverse's proved identity, avoiding a second comparison of the
same chart structures that had reopened quotient induction. The section
composite is split at its intermediate section images, as in the text.
Finally the reconstruction triangle is checked at the defining glued
space; this reduced its distinct openings from 74 to 29 and avoided
rechecking component proofs through a second presentation.

Validation after these repairs:

- `unit/segc unit/sag/qcqs all`: 191 modules, zero failures (6.02 s in
  the full run; subsequent affected-module checks also pass).
- Independent full `seg All.seg --opens essential-image.opens`:
  7,629 declarations, zero failures (8.50 s).
- Every one of the 2,131 OPENS lines explicitly says
  `nothing else opened`; extra openings are checked separately from
  the process exit code.
- The 12 new modules have 397 audited declarations. Each new declaration
  takes at most 0.05 s in the isolated audit; at most 49 distinct names
  are opened, in AtlasSections.At.second (the explicit comparison of
  the equaliser's second leg with ambient restriction).
- The mathematical note compiles successfully. No new axiom; no edits
  to core or sag/categories. Existing uncommitted work is preserved,
  and this continuation is also left uncommitted.

### Previous continuation boundary (categorical item completed below)

The absolute essential-image theorem and the transition cocycles are
complete. The existing absolute Hom--Nat comparison together with
EssentialImage gives full faithfulness and mere essential surjectivity.

The remaining work is separate:

1. Relative totalisation over a base ring, followed by recovering the
   structure map and taking fibres (Section 7 of the note).
2. Packaging the geometric category and proving its univalence, before
   claiming a literal equivalence of univalent categories.

Neither item is an assumption of the absolute theorem just checked.


### Informal categorical comparison (2026-10-29; formalised below)

Section 8 of `unit/doc/functorial-schemes.tex` now gives the informal
proof of equivalence of univalent categories and its review. It proves
structured identity principles for locally ringed lattices and for
set-valued functors, then restricts to the propositional qcqs properties.
Full faithfulness makes the object map an embedding; essential
surjectivity inhabits its propositional fibres after truncation
elimination. Conjugation by the resulting counit isomorphisms and the
Hom--Nat inverse define a quasi-inverse functor.

This section is an informal proof, not an additional checked `.seg`
theorem. Geometric and functorial category packaging, their structured
identity principles, and the assembled categorical equivalence still
need formalisation. The checked absolute essential-image theorem and
its opening audit are unchanged. The updated PDF compiles successfully.


## Equivalence of univalent categories checked (2026-10-29)

The informal proof and review in Section 8 of
`unit/doc/functorial-schemes.tex` are now formalised. The final theorem is
`QcqsCategories.equivalence`. Its type is the categorical equivalence
record of CategoryQuasiInverse, containing an actual inverse functor,
component isomorphisms for both composites, and both naturality proofs.
Both source and target are constructed univalent category records;
univalence is not an additional assumption of this theorem.

### Structure identity and categorical univalence

The proof uses the existing SipGeneric, Category, Arrows, Functor and
EquivalenceLemmas through local symlinks. Their sources are unchanged.

- IdentityTools proves the elementary proposition lemmas, including
  uniqueness of bi-invertibility witnesses between sets.
- RingIdentity and LatticeIdentity apply SipGeneric to the actual
  commutative-ring and bounded-distributive-lattice records. Their
  equation laws over sets are propositions. Explicit field/reconstruction
  maps and record induction give the required retractions.
- FamilyIdentity passes an identity system to indexed families and
  supplies right induction. DecoratedIdentity extends one by structure
  or by a propositional property. The proofs use contractible total
  spaces and reuse SipGeneric.Fundamental.
- PresheafIdentity handles the ring family, restriction maps and their
  laws. On the identity ring-family isomorphism, naturality identifies
  the restriction maps by extensionality. LocalIdentity adds sheafhood,
  invertibility maps and support laws as a proposition. In particular
  uniqueness of invertibility opens is used; an arbitrary extra support
  operation is not silently discarded.
- SpaceIdentity handles the dependent lattice/structure pair, retaining
  the contravariant direction of geometric maps. SpaceIsoIdentity takes
  every actual isomorphism to this structural presentation together
  with equality of the underlying ringed maps. Replacing a lattice map
  by its structured presentation transports the WHOLE ringed map along
  their equality; lattice iso induction and ring Hom-of prove agreement.
- GeometricCategory proves that the bijectivity criterion and the
  categorical two-sided-inverse criterion agree. Its categorical
  singletons retract onto the contractible structural total spaces;
  Category.FromTotal gives univalence for the existing category of all
  spaces and local geometric maps.
- SetIdentity, FunctorIdentity and FunctorCategory give the corresponding
  proof for existing small-set-valued functors and natural transformations.
  Structural functor isomorphisms and NaturalEquivalence are the same
  component data, reordered, with the original natural map retained.
- FullSubcategory restricts a univalent category to any propositional
  property, inheriting its arrows and operations. This gives the two
  univalent qcqs categories without chosen atlases in their objects.

### Comparison and inverse

QcqsCategories.functor is the existing functor of points: GeometricAtlas
supplies the object property, FunctorPoints.induced supplies the arrow
map, and geometric units/associativity prove its laws. PointsUniversal
supplies fully-faithful. EssentialImage.reconstruct, followed by inversion
of its representing equivalence, supplies essentially-surjective.

WeakCategoryEquivalence proves the general unsplit theorem. Full
faithfulness gives an equivalence on isomorphism types. The functor's
idtoiso square is path induction; univalence on both sides identifies
its object-path map as an equivalence. EmbeddingFibres therefore makes
every object fibre a proposition. Mere essential surjectivity inhabits
that fibre after converting isomorphisms to paths. Truncation elimination
is now valid, and the resulting section and retraction give the object
equivalence. No global choice of representatives is assumed.

CategoryQuasiInverse constructs the inverse functor from those unique
fibres. Its arrow map is the unique lift of conjugation by the counit
isomorphisms. Functor.Faithful.lift-eq gives its defining square;
Functor.Faithful.unique and paste prove identity and composition. The
same square is counit naturality. Reflecting the counit at H(X) gives
the unit isomorphism, whose naturality follows by faithfulness. The
Equivalence record packages this quasi-inverse and both natural
isomorphisms. QcqsCategories.equivalence instantiates it, while
QcqsCategories.object-equivalence separately records the equivalence
of object types.

### Validation and continuation

- Full server check: 214 modules, zero failures (6.58 s).
- Independent full checker with the combined essential-image.opens and
  categories.opens lists: 8,387 declarations, zero failures (9.59 s).
- All 2,889 OPENS lines explicitly say `nothing else opened`; zero extra
  openings. The new categories.opens file records 758 declarations:
  591 in the 18 new modules and 167 in the five reused source modules.
- Isolated opening audit: each audited declaration takes at most 0.01 s;
  the largest opens 24 distinct names (RingIdentity.fields, the explicit
  record-to-structure presentation). No construction proof is reopened
  in the comparison clients.
- The mathematical note and PDF are updated and compile successfully.
  No new axiom, no resizing or choice principle, no core or category
  refactoring. All earlier uncommitted work is preserved and all new
  work remains uncommitted.

To reproduce the combined audit from qcqs, concatenate
`essential-image.opens` and `categories.opens` into a temporary file,
then run `seg All.seg --opens` on that file. Besides checking the exit
status, verify that every OPENS line says `nothing else opened`.

The absolute equivalence of univalent categories is complete. The
remaining comparison work is the relative totalisation theorem over a
base ring, as described in Section 7 of the note. It is not an assumption
of the absolute categorical equivalence.


## Final relative checkpoint — 2026-10-29

The relative totalisation theorem and the relative equivalence of univalent
categories are complete. The detailed informal argument was written and
reviewed in `../../doc/relative-totalisation.tex` before formalisation.
Its sections follow the formal declarations, including the intermediate
transport, matching, and inverse-law steps. The three LaTeX documents
and PDFs are updated after completion of the formalisation, as requested.

### Intrinsic relative objects and dependent transport

The tests are the existing BasePoints.Algebra objects `(B, i : K → B)`
and their actual commuting algebra maps. RelativeFunctors and
RelativeSheaves define the native functor and algebra-cover sheaf
condition. RelativeQcqs defines the native finite affine atlas and qcqs
condition intrinsically, before proving the criteria via totalisation.

DependentPairs gives transport, composition and inverse transport,
pair-equality, fibre-equality over a specified base path, and rebase-pair.
Sethood of the base identifies the extracted path with the specified
path; dependent second projections are never compared without transport.
RelativeTests names canonical algebra lifts, their evaluation equations,
and commuting-path. RelativeTotal.change-target is path induction on
that base equation; on-algebra states the action on an arbitrary genuine
algebra map. Identity and composition use this interface.
RelativeTotalMaps proves totalised naturality, its base equation, and
identity and composition laws.

RelativeCovers first proves the pointwise base square and then the square
of algebra maps. RelativeCoverFibre pairs native families and extracts
compatibility over a fixed base. RelativeBaseGlue projects a compatible
total family to the representable base, glues that base, rebases each
local value backwards along its matching path, and retains the whole
pair equation. RelativeTotalSheaf then uses native gluing and uniqueness.
RelativeSheafOfTotal gives the converse using total gluing and separation
of the representable base before extracting a native amalgam.

RelativeOpens compares native and total opens, with inverse laws, and
RelativeRealisationTotal compares their realisations. RelativeTotalAffine
compares a native representable's total with an absolute representable.
For the converse RelativeAffineOfTotal extracts the algebra structure
at the generic point, names the base equation, transports the value,
and retains its total-point trace for naturality and both inverse laws.
RelativeTotalQcqs and RelativeQcqsOfTotal transfer affine atlases and
sheafhood in the two directions. The final interface is
`RelativeTotalisation.Over[K,F].sheaf-equivalence` and `qcqs-equivalence`.

### Reconstruction and categories

RelativeFibres recovers a native functor from `G → h_K`.
TotalFibreEquivalence proves its total is equivalent to G over h_K;
RelativeFibreRecovery proves that taking fibres of a total recovers F.
Both proofs retain the displayed base path, including in their inverse
laws. RelativeFibreEquivalence restricts equivalences over the base.
RelativeGeometric reuses the existing geometric points over Spec K.
GeometricBaseRecovery recovers a structure map from a natural map to h_K;
RelativeGeometricFibre compares its fibres with those geometric points.

RelativeEssentialImage applies the absolute reconstruction to the total,
recovers the structure map, then composes the three native equivalences.
Mere existence is eliminated only into the proposition of mere relative
representation. Its reconstruct and recognise maps give the equivalence
between intrinsic native qcqs and mere representation by a qcqs space
over Spec K. RelativeQcqsTransfer and RelativeGeometricQcqs provide
invariance and the geometric example.

RelativeFunctorIdentity and RelativeFunctorCategory establish univalence
for the native functors on the fixed existing algebra-test type.
SliceCategory proves univalence of the actual slice, retaining its
commuting equation; it uses the decorated identity system and the
contractibility of `(t, t·id=s)`. RelativeCategories uses that geometric
qcqs slice and the full subcategory of intrinsic native qcqs functors.
Existing RelativeUniversal supplies full faithfulness; the new relative
essential image supplies essential surjectivity. The existing generic
WeakCategoryEquivalence and CategoryQuasiInverse then give
`RelativeCategories.Over[K].object-equivalence` and `equivalence`.
The latter contains an inverse functor and both natural isomorphisms.

### Opening review and validation

The isolated review found and repaired three interface leaks without
changing the core or category library:

- Lock RelativeTests.commuting-path after its interface so on-algebra
  does not recompute the function-extensionality construction.
- State left/right commuting and base-square equations pointwise using
  push-at and compose-at, then apply algebra-map extensionality. This
  avoids reopening localisation and fraction constructions.
- State the geometric fibre inverse's back-point equation and lock back
  before proving its inverse laws. Clients use that equation rather
  than reopening the proof of its base equality.

The final checks, after all source edits:

- Full server: **249 modules, zero failures**, 6.70 s.
- Independent full checker: **9,250 declarations, zero failures**, 10.07 s.
- Combined opening audit: **3,752 lists, all explicitly reporting
  `nothing else opened`**, zero extra openings.
- The 35 new modules contribute **863 audited declarations** in
  `relative.opens`. The isolated maximum is 0.05 s per declaration and
  33 distinct opened names. No construction proof of function
  extensionality, quotients or localisation is reopened by these clients.

Reproduce the server check with `unit/segc unit/sag/qcqs all` from the
repository root. For the independent audit concatenate
`essential-image.opens`, `categories.opens`, and `relative.opens` into a
temporary file, then run the unit checker on `unit/sag/qcqs/All.seg` with
`--opens` pointing at that file. Verify every OPENS line as well as the
exit status. Imports remain local to qcqs; no new axiom, resizing, choice,
core change or category-library refactoring is involved. Earlier
uncommitted work is preserved, and the development remains uncommitted.

There is no remaining proof obligation in the requested absolute and
relative comparison programme. The current detailed proof is
`../../doc/relative-totalisation.pdf`; the broader account is
`../../doc/functorial-schemes.pdf`, and the categorical theorem appears
in `../../doc/univalent-categories.pdf`.
