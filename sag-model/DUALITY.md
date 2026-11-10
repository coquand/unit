# The SAG axioms in the presheaf model: a conditional verification

Ruling (2026-11-10): the immediate goal of the SAG-model work is a
checked proof of the three presheaf axioms of jonas.pdf §6.3 in
PSh(C)_DT: duality (Axiom 2, **Theorem 62**) first, then constancy of N
(Axiom 3, **Theorem 61**) and projectivity of spectra (Axiom 1,
**Prop 76**). The proofs are checked relative to named premises, each with
an exact statement and a status. Numbering refers to jonas.pdf (Höfer,
licentiate, `~/COLL/jonas.pdf`): §4 (cobar), §6.4–6.5, Appendix A.

## 0. What "completed" means, and what is deferred

**Endpoints.** Every step is checked in Unit, under the premises of
Section 3.
- **E1 (Axiom 2, Theorem 62).** For every u : Pr_{T/G,Dκ} the transposed
  evaluation ⟨u⟩_{T/G} → G^{Sp(⟨u⟩)} is an equivalence in PSh(C)_DT.
- **E2 (Axiom 3, Theorem 61).** For every u : Pr_{T/G,Dκ} the constant
  map N → N^{Sp(u)} is an equivalence in PSh(C)_DT.
- **E3 (Axiom 1, Prop 76 at Sp).** Sp(u) is projective (Definition 73).

The axioms quantify over Dκ-presentable algebras; the paper notes they
are logically equivalent to the versions with a given presentation u,
which are the ones stated here. A premise has one of three statuses:

- **proved here**: a checked Unit file of this plan;
- **Unit theorem**: an existing checked Unit file (path given);
- **semantic**: an assumption about the model, to be instantiated later.

E1–E3 are not a model of SAG and not a model of Unit.

**Deferred (unchanged, not abandoned).**
- The complete-model endpoint of `README.md` / `INTERFACE.md` (M0–M5):
  a checked semantic inhabitant of the interpreted `SAGAxioms.Assumptions`,
  with the Theory parameters discharged. Its definition of "completed" is
  kept as written there. M1 steps 4–6 (`M1.md`) belong to it.
- S4 (the univalence bridge, `M1.md` "Step 3, S4") stays at its last
  checked state. It is not extended for E1–E3.

**Work split (coordinated from canonicity-4e, 2026-11-10).**
- canonicity-45: Tier 2 (the record T2 in `unit/sag/duality-presheaf`,
  P2.1–P2.5), then E2 (Theorem 61: Tier 5 below).
- canonicity-4e: Tier 1 (done), Tier 3 (P3.1–P3.6 on top of T2), Tier 4
  (E1), then E3 (Tier 6 below).

## 1. The proof of Theorem 62, as a dependency spine

1. (Prop 17, externalised) An equivalence of D-modal types is the same as
   a levelwise equivalence. So it suffices to show, internally to cSet,
   that each component (λev)_{(A,u)} is an equivalence.
2. (Remark 60 + Lemma 59) The component (λev)_{(A,u)} sits in a strictly
   commuting square whose right side is an equivalence (Lemma 59 at the
   local representation of Sp, Prop 58). By 2-out-of-3 it suffices that
   ev_{(⟨u⟩, u p, q)} ∘ ⟨−⟩(p_u) is an equivalence.
3. (Constructions 56, 57; Remark 46) This composite is identified, up to
   homotopy, with q_u ∘ p_u^+ : ⟨u⟩ → ⟨u p_u⟩ → ⟨u⟩ in the base.
4. (Tier 1) q_u ∘ p_u^+ ~ id. Hence the composite is an equivalence.

Steps 1–2 are Tier 2, step 3 is Tier 3, step 4 is Tier 1, and the assembly
is Tier 4.

## 2. The tiers

### Tier 1: the algebra in the base (no model)

Statements internal to cSet that are ordinary univalent algebra, checked
in Unit directly, in `unit/sag/duality` (symlinks to `sag/presentations`
and `sag/tensor`; nothing in sag-model).

Generic form: algebras A, P with p : A → P, and B. A *base change* of p
along h : A → B is a pushout square (`tensor/Pushout.seg`,
`Square[P,B,A,p,h].Pushout Q`): maps h^+ = inA : P → Q, j = inB : B → Q.

| Item | Paper | Statement | File |
|---|---|---|---|
| T1.1 | Lemma 50, laws | comparison map between two base changes along k with k h₁ = h₂; its uniqueness; identity and composition laws | `BaseChange.seg` |
| T1.2 | before Prop 58 | q : the common retraction of j and h^+ for h = p (B = P): q h^+ = id, q j = id | `BaseChange.seg` |
| T1.3 | Prop 58 (base part) | given a base change ch h for every h : A → B, the explicit map forward : Hom(P,B) → Σ (h : Hom(A,B)) Ret_B(ch h), r ↦ (r p, the retraction induced by (r, id_B)), is an equivalence | `Representability.seg` |
| T1.4 | Construction 57 (evaluation clause, base part) | evaluation equation: (forward r).2 (h^+ y) = r y | `Representability.seg` |
| T1.5 | Lemma 50, instance | presentations give base changes (`tensor/Pushout.seg` Construction, at chosen presentations; no elimination from truncated FP witnesses) | Unit theorem: `sag/tensor/Pushout.seg` |

Ret_B(Q, j) = Σ (r : Hom(Q,B)) Π b. r (j b) = b (pointwise, as the cocone
condition of `Square`).

Foundation actually used by Tier 1: the Theory parameters of
`sag/tensor/All.seg` (univalence, replacement images, surjectivity). The
generic files T1.1–T1.4 use only funext (from univalence) and the pushout
property; replacement enters through T1.5 (quotients in
`PresentationExistence`).

### Tier 2: the modal Yoneda lemma (abstract)

One record `T2` over a presheaf CwF on a small strict category C internal
to the base, with D: the fields are S2.1-S2.6 (Section 3). Proved from it
(**proved here**), in this order:

| Item | Paper | Statement | Uses |
|---|---|---|---|
| P2.1 | Lemma 66 | if S2.5 is not a field: in a diagram A0 -s0-> B0 -r0-> C0 over A1 -s1-> B1 -r1-> C1 of homogeneously fibrant types with vertical a, b, c and homotopy-commuting squares, if r0 s0, r1 s1 and b are equivalences then so are a and c | S2.1, S2.2 |
| P2.2 | Lemma 67 | f : A -> B a levelwise equivalence of levelwise fibrant types, Q a fibrant D-modal family over B: f* : Π(b:B) Q b -> Π(a:A) Q (f a), g ↦ g ∘ f, is an equivalence | S2.2-S2.5, P2.1 |
| P2.3 | Prop 69 | δ : ょx -> Δ a homotopy representation (levelwise equivalence) of a levelwise fibrant Δ, P : Ty^D(Δ): El(Δ, P) -> P(x, δ), u ↦ u(x, δ), is an equivalence | S2.1, P2.2 |
| P2.4 | Lemma 72 (= 59) | A : Ty^Fib0(Γ) with a local homotopy representation (x.γ, p_γ, q_γ) (Def 70, strictly stable: Remark 71), P : Ty^D(Γ.A): (Π_A P)(x, γ) -> P(x.γ, γ p_γ, q_γ), u ↦ u_{p_γ}(q_γ), is an equivalence | S2.1, P2.3 |
| P2.5 | Remark 60 | for S : Ty^Fib(Γ) and f : Sp_A -> P over ∫Γ.A, the square λf_(x,γ) ; ev_{p,q} = f_(x.γ, γp, q) ∘ S(p_γ) commutes **strictly**; so λf_(x,γ) is an equivalence iff f_(x.γ,γp,q) ∘ S(p_γ) is | S2.1 (strict Π-β), P2.4 |

The record carries the dependent structure Lemma 67's diagram uses (the
family action D̃Q, τ*_B, and the iso of the horizontal composites with Π's
functorial action on τ_{Q(b)}), so that no step meets an unnamed premise.
It is not a complete abstract model.

### Tier 3: the levelwise identification

Internal to cSet, naturally up to homotopy in A : Mod_{T,κ}. Proved here
from S3.1-S3.6 and Tier 1:

| Item | Paper | Statement | Uses |
|---|---|---|---|
| P3.1 | Construction 51 | Mod(UΓ)(U A, B) ≅ Mod(Γ)(A, R B) over Remark 7's iso, natural in Γ, up to homotopy in A, B | S3.1 |
| P3.2 | Lemma 52, Cor 53 | U preserves free T-models, coproducts and coequalisers of T-models up to equivalence; U sends G-algebras to G₀-algebras and their free / coproduct / coequaliser constructions to those of G₀-algebras | S3.1, S3.2, S3.5, P3.1 |
| P3.3 | Construction 55 | Pr_{T/G,Dκ}(A) ≃ Pr_{T/A,κ} | S3.3, S3.4, S3.6, P3.2 |
| P3.4 | Construction 56 | over P3.3: Σ_{Pr_{T/G,Dκ}(A)} ⟨−⟩_{T/G}(A) ≃ Σ_{Pr_{T/A,κ}} ⟨−⟩_{T/A}, fibrewise an equivalence of T-models | P3.2, P3.3, S3.4 |
| P3.5 | Construction 57 | over P3.3: Σ_{Pr_{T/G,Dκ}(A)} Sp(A) ≃ Σ_{Pr_{T/A,κ}} Ret_A; **the clause to check exactly**: under this, Remark 46 and P3.4, the evaluation map of Sp is homotopic to ev_{A,u} : Ret_A(u) × ⟨u⟩_{T/A} -> A, (r , y) ↦ r y — not merely some equivalence of objects | P3.2-P3.4, S3.5 |
| P3.6 | Prop 58 | Sp : Ty(1.Pr_{T/G,Dκ}) is locally homotopy representable: at A and u the representation is ⟨p_u , q_u⟩ : ょ⟨u⟩_{T/A} -> ょA.Sp(u) under P3.5 | P3.5, S3.6, T1.2-T1.5 |

Phrasing of P3.6 for Tier 1. Its base part is cited at P := ⟨u⟩_{T/A},
p := p_u directly (Tier 1 now presents over A, commit f81b5c4f):
RelativeChange.Chosen[A, u, X, px].ch gives the base change of p_u along
every h (no truncation), Points.Spectrum[A, u, X, px, B].spectrum is
Hom(⟨u⟩, B) ≃ Σ (h : Hom(A, B)) Solutions(u h, B) with `generators` (the
solution of r is r on the generators), and Points.Points gives Ret =
Solutions with `values` and `evaluation`. T1.3/T1.4 (`forward`,
`evaluation`) are the same statements for a generic p. Ret is pointwise
(Π b. r (j b) = b), which at sets is the paper's r ∘ p ∼ id.

### Tier 4: assembly

Statement (E1), internal to PSh(C)_DT: for u : Pr_{T/G,Dκ}, the
transposed evaluation λev : ⟨u⟩_{T/G} -> G^{Sp(⟨u⟩_{T/G})} is an
equivalence. Externalised form actually proved (via S2.6):
El_{cSet}(1.C₀.U Pr_{T/G,Dκ}, is-equiv(U(λev))). Proof: at (A , u), P2.5
with S := ⟨−⟩_{T/G}, P := G (D-modal) reduces to ev_{(⟨u⟩, u p, q)} ∘
⟨−⟩_{T/G}(p_u); by P3.4-P3.6 this is homotopic to q_u ∘ p_u⁺; Tier 1
(T1.2: q_u p_u⁺ ~ id) and 2-out-of-3.

### Tier 5: E2, constancy of N (Theorem 61)

At (A, u): the square of Remark 60 (P2.5) for S := N_DT and
f := π₁ : N × Sp(u) → N, with the left square given by naturality of
τ_{ΔN}; the components of τ_{ΔN} are equivalences (S3.4 at ΔN), the right
side is Lemma 59 (P2.4) at the local representation of Sp (P3.6); by
2-out-of-3 the component of λπ₁ is an equivalence; S2.6 concludes.
New premise: S2.7.

### Tier 6: E3, projectivity of Sp (Prop 76)

Being locally homotopy representable is stable under substitution
(Remark 71, in T2), so it suffices to take P ∈ Ty^DT(Γ.A). The map
El(Γ, Π_A ∥P∥) → El(Γ, ∥Π_A P∥) is: Π's universal property; Prop 34
left-to-right; internally to cSet, restriction along (x.γ, γp_γ, q_γ)
followed by the inverse of Lemma 72 (P2.4) under ∥−∥; Prop 34
right-to-left. Applied at A := Sp over Pr_{T/G,Dκ} via P3.6.
New premises: S3.7, S3.8.

## 3. Premises

### Tier 1

| # | Statement | Consumers | Status |
|---|---|---|---|
| S1.1 | Univalence, replacement images, surjectivity as the Theory parameters of `sag/tensor/All.seg` | T1.5 (quotients) ; T1.1–T1.4 use only `fe` | Unit premise (as all of sag/) |

### Tier 2 (all **semantic**, to be instantiated at the poset base)

Equations column: **ext** = external (judgemental) equality of the CwF,
stated with `Id` of the metatheory on contexts / types / elements;
**path** = an internal identification (Swan Id or a homotopy); **map** =
an external function between types of structures (the paper's "there is
a map"), natural in Γ with ext stability under substitution.

| # | Statement | Equations | Consumers |
|---|---|---|---|
| S2.1 | PSh(C) over a small strict category C internal to the base (unit, associativity: ext): contexts, types, elements, substitution, Π (β, η), Σ, Id, the representables ょx and the context extensions ょx.Aγ, all strictly stable under substitution | ext (all CwF laws, Π-β and η: Remark 60's square is strict) | everything in Tier 2 |
| S2.2 | Fibrant, levelwise fibrant, homogeneously fibrant types; levelwise equivalence (U f an equivalence, pointwise); homotopy; Π over any domain with homogeneously fibrant codomain is homogeneously fibrant; functorial action of Π on a family of maps respects homotopies; precomposition with an equivalence between fibrant types induces an equivalence of Π-types with fibrant codomain (Rijke 13.4.1) | definitions: ext; the two invariance statements: path (internal equivalences) | P2.1, P2.2 |
| S2.3 | D on contexts, types and families (DΓ, DA, D̃Q over DB), the unit τ_A : A -> DA, its naturality D f ∘ τ_A = τ_B ∘ f, the comparison τ*_B of D̃Q along τ_B, D-modal := τ_Q is an equivalence; stable under substitution; the horizontal composites of Lemma 67's diagram are isomorphic to Π's functorial action on (τ_{Q b})_b | stability, naturality of τ, the isos: ext; D-modality: path (is-equiv) | P2.2, S2.6 |
| S2.4 | (Lemma 12 corrected, Prop 13) maps Fib(UΓ, UA) -> Fib(DΓ, DA) and Fib(UΓ, UA) × Fib(UΓ, UB) × El(UΓ, is-equiv(U f)) -> El(DΓ, is-equiv(D f)) | map (into a path: is-equiv) | P2.2 |
| S2.5 | (Lemma 66) as P2.1 | path (homotopies of the squares suffice) | P2.2 |
| S2.7 | (§6.5) the natural numbers of PSh(C)_DT are, up to equivalence, N_DT := D(ΔN), the D-modal replacement of the constant presheaf on N, with τ_{ΔN} natural | the equivalence: path; naturality of τ: ext | Tier 5 |
| S2.6 | (Prop 17) naturally in Γ, for A, B : Ty^D(Γ), f : A -> B: El(UΓ, is-equiv(U f)) <-> El(Γ, is-equiv f) | map (both directions; logical, not an iso), naturality ext | Tier 4 |

S2.5 may become **proved here** (P2.1) if its proof is elementary in the
record; then S2.5 is dropped, not kept beside P2.1.
Consistency check (canonicity-4e): D = id makes S2.1-S2.5 provable for
plain presheaves; S2.6 then fails for non-discrete C, so the D = id check
covers S2.6 only with C discrete.

### Tier 3

All **semantic**. Same Equations legend.

| # | Statement | Equations | Consumers | Status |
|---|---|---|---|---|
| S3.1 | U ⊣ R (Remark 7): R on contexts, types (R A := (R A)η_Γ), elements; the iso El_{PSh(C₀)}(UΓ, A) ≅ El_{PSh(C)}(Γ, R A), natural in Γ; its extension to hom-types and homotopies; the dependent R_Γ B over Γ.R A with R(Σ_A B) ≅ Σ_{RA} R_Γ B and R(B p_A) = (R B) p_{RA}; U and R preserve the T-model structure, unit and counit are strict homomorphisms | the isos and their naturality: ext; transposition of homotopies: path | P3.1, P3.2 | semantic |
| S3.2 | Existence, in PSh(C)_DT and in cSet_T↓C₀, of free T-models, coproducts and coequalisers of T-models with their universal properties (as equivalences of hom-types of models), in families and stable under substitution (the adjunction only gives preservation once these exist) | universal properties: path (equivalences); stability: ext | P3.2 | semantic |
| S3.3 | (Lemma 54) U preserves dependent products with domain in (κ, El_κ): for I : κ, U(Π_{El_κ I} B) ≃ Π_{El_κ I} U B, natural in Γ | path (an equivalence suffices downstream: P3.3-P3.5 are up to homotopy); naturality: ext | P3.3-P3.5 | semantic |
| S3.4 | (Lemma 14) Fib(UΓ, UA) -> El(UΓ, is-equiv(U τ_A)); in particular at El_κ in context κ | map (into is-equiv); the strict retraction ε τ = id of its proof is not needed | P3.3, P3.4 | semantic |
| S3.5 | (Remark 46) G₀(A) := A; U G ≃ G₀ as T-models in PSh(C₀) | G₀ by definition: ext; the equivalence and its preservation of the model structure: path | P3.2, P3.5, Tier 4 | semantic |
| S3.6 | (Construction 39, Lemma 40, Lemma 42, Remark 38) the small strict category C, C^op ≃ Mod_{T,κ}, κ-presentable A-algebras are κ-presentable, smallness, the classifier (Dκ, D̃El_κ). (The over-R / over-A comparison is no longer needed: Tier 1 presents over A.) | C's unit and associativity: ext; Lemma 40, Lemma 42: path | P3.3, P3.6 | semantic |
| S3.7 | Propositional truncation ∥−∥ in PSh(C)_DT and in cSet_T↓C₀ (types, the truncation map, the universal property into propositions, is-prop), stable under substitution | stability: ext; universal property: map | Tier 6 | semantic |
| S3.8 | (Prop 34) naturally in Γ, for A ∈ Ty^DT(Γ): El(UΓ, ∥UA∥) <-> El(Γ, ∥A∥) (logical equivalence; its proof uses Theorem 29, Lemma 12 and R) | map (both directions), naturality ext | Tier 6 | semantic |

## 4. After E1–E3

Instantiating Tier 2 and Tier 3 premises at the poset base needs the
cobar D (S2.3–S2.6), and also algebraic existence and smallness (S3.2,
S3.6): internal free algebras and quotients in the base. So the later
discharge is not "only cobar"; parts of M1 step 6 return there, but not
M1 steps 4–5 in full, nor the univalence bridge.

**Reading of the premises (ruling 2026-11-10, reading (A)).** Tiers 1–6
are written in Unit read as the homotopical internal language of cSet,
as the paper's Appendix A and §6.4 are internal to cSet: the model
PSh(C) is a record whose substitutions and elements are Unit types and
whose CwF laws are Unit paths, with no higher coherence fields (used only
into propositions or equivalences); "levelwise" means fibrewise at the
points El(ょx, −), and contexts are levelwise fibrant. Instantiating at
the actual model therefore has two further obligations, besides the
premises themselves: (i) the internal–external passage (an
interpretation of these Unit statements in cSet); (ii) the strict laws
of the model supply the paths (by refl), and every place where a proof
would need a 2-cell between law-paths is reported, not assumed.

## 5. Status

- 2026-11-10: plan written. Tier 1 T1.1-T1.5 checked in `unit/sag/duality`
  (BaseChange, Representability, Presented; 36 modules, 0 failed, 0.16 s).
  No new axioms beyond the Theory parameters of `sag/tensor`.
- Split: Tier 1 by this session; the premise interface (Tiers 2-4, (a) the
  site C as data, (b) D abstract, (c) Theorem 62 in P) drafted by the
  canonicity-45 session in a new directory.
- 2026-11-10 (later): Tier 1 extended to presentations over A
  (`Relative`, `RelativeChange`, `Points`; 39 modules, 0 failed, 0.18 s):
  Lemma 50 at P = <u>_{T/A}, p = p_u with a chosen base change for every
  h; Ret_B(u.h) = Solutions(u.h, B) with evaluation; and
  Hom(<u>, B) = (h : Hom(A,B)) * Solutions(u.h, B), r |-> (r p_u, r on
  the generators).  The over-R/over-A caution of S3.6 is resolved at the
  base level.
