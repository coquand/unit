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

Checked (`../../segc qcqs all`: 49 modules, 0 failed, about 0.5 s):

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
