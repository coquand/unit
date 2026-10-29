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
