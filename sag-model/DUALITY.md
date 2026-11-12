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
  (E1, done conditionally).
- Reassigned 2026-11-10 after E2: canonicity-45 takes E3 (Tier 6);
  canonicity-4e takes P3.6, then Tier 3 step 3 (P3.3–P3.5 from S3.1–S3.5).

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
| P3.3 | Construction 55, syntactic form (ruling 2026-11-10) | G₀ is the context of syntactic presentations (n : N) * List(Expr_G(Fin n)); its points at x are Tier 1's presentations over alg x, compatibly with restriction (u ↦ u·h). Follows from S3.9. (The paper's Construction 55 is the polynomial-presentation analogue; polynomial presentations have no map back to syntax without choice, so the syntactic form, which SAGAxioms.seg uses, is taken.) | S3.10 | (`E1.Mods`) ⟨−⟩_{T/G} and G are D-modal over G₀, G, Sp and ⟨−⟩_{T/G} (`Br-fib`, for Prop 17) are fibrant (paper: G is DT-modal by Theorem 29 and Remark 46; presented models are colimits in PSh(C)_DT; hom-types of models into a modal type are fibrant) | path (D-modality, is-equiv) | E1–E3 | semantic |
| S3.9 |
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

#### Tier 3 in reading (A): the interface T3 and the order of work

U is "take fibres" (T2's `Der.Pts`: points pts Γ x, fibres fib Γ A x g).
The tree is `unit/sag/duality-levelwise` (symlinks to T2 and Tier 1,
read-only). The work runs in three steps, so that E1 is checked end to
end before the deepest step:

1. **The record T3 (statement level).** Over T2's model, with R-algebras
   from Tier 1:
   - from S3.6: alg : Ob -> Algebra with Hom y x ≃ Hom(alg x, alg y),
     and an object ⟨u⟩ of C for every presentation u over alg x;
   - from P3.3: a context Γ₀ (= 1.Pr_{T/G,Dκ}) whose points at x are
     the presentations over alg x, compatible with restriction (u ↦ u·h);
   - from P3.4: a type Br over Γ₀ whose fibre at u is the carrier of the
     presented algebra ⟨u⟩ (Tier 1's X), with restriction acting as h⁺;
   - from S3.5: a type Gt whose fibre at x is alg x;
   - from P3.5: a type Sp whose fibre at u is Points.Ret, and ev over
     Γ₀.Sp whose action on fibres is (r , y) ↦ r y (**the clause**);
   - Br and Gt D-modal, and Sp fibrant.
2. **P3.6 and Tier 4 from T3, proved.** These are the local
   representation of Sp from Tier 1 (`Points.Spectrum`,
   `RelativeChange.Chosen`), and E1 from P2.4, P2.5, Prop 17 and
   Modal-Pi. After this step, E1 is checked relative to T2 + T3.
3. **T3 from S3.1–S3.5 (P3.1–P3.5 proved).** This is the generic
   transfer along U ⊣ R (left adjoints preserve objects given by
   universal properties: free, coproduct, coequaliser), then the
   fibrewise identifications. Until this step is done, P3.3–P3.5 have
   status *stated, proof pending*.

### Tier 4: assembly

Statement (E1), internal to PSh(C)_DT: for u : Pr_{T/G,Dκ}, the
transposed evaluation λev : ⟨u⟩_{T/G} -> G^{Sp(⟨u⟩_{T/G})} is an
equivalence. Externalised form actually proved (via Prop 17, `Prop17.seg`):
El_{cSet}(1.C₀.U Pr_{T/G,Dκ}, is-equiv(U(λev))). Proof: at (A , u), P2.5
with S := ⟨−⟩_{T/G}, P := G (D-modal) reduces to ev_{(⟨u⟩, u p, q)} ∘
⟨−⟩_{T/G}(p_u); by P3.4-P3.6 this is homotopic to q_u ∘ p_u⁺; Tier 1
(T1.2: q_u p_u⁺ ~ id) and 2-out-of-3.

### Tier 5: E2, constancy of N (Theorem 61)

At (A, u): the square of Remark 60 (P2.5) for S := N_DT and
f := π₁ : N × Sp(u) → N, with the left square given by naturality of
τ_{ΔN}; the components of τ_{ΔN} are equivalences (S3.4 at ΔN), the right
side is Lemma 59 (P2.4) at the local representation of Sp (P3.6); by
2-out-of-3 the component of λπ₁ is an equivalence; Prop 17 (`Prop17.seg`) concludes.
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

Reading (A) (agreed 2026-11-10): internal to cSet, Unit being its
internal language, as Tier 1. Fields of the records of
`unit/sag/duality-presheaf/T2.seg`. Equations legend: **ext** now means a
Unit Id, an internal path (the strict version is an instantiation
obligation, §4); **map** = a function into is-equiv, natural in Γ.

| # | Statement | Equations | Consumers |
|---|---|---|---|
| S2.1 | `PCwF`: contexts, Sub and El as Unit types (no isSet), Ty with **isSetTy** (types form a set: the homotopical shadow of judgemental type equalities, as in 2LTT; constrains instantiation, §4; used only through `TE.teAny`, by `Lemma72.lpt-ext` and the exchange of Remark 60), substitution, subt-id (terms along the identity, the law matching subT-id; added 2026-11-10 for Prop 17), ext, p, q, pair, p-pair, q-pair (over wkp), pair-eta; `Site`: C, yo x, yoH, its functor laws and yoH-eq (Yoneda: Hom(y, x) ≃ Sub(yo y, yo x)); `PiS`: Π, lam / app inverse (app-lam, lam-app), Pi-nat (along lift), lam-nat (lam stable under substitution, as a TE) | ext | everything in Tier 2 |
| S2.2 | `DS`: Fib and Fib-sub; internal equivalences IsEqC (context maps), IsEqT (maps of types); restr-eq: precomposition with an internal equivalence is an equivalence on elements of a fibrant type (Rijke 13.4.1 through PSh(C)(1,−)); post-eq: an internal equivalence of types acts as an equivalence on elements (PSh(C)(D,−) preserves equivalences) | map | P2.2 |
| S2.3 | `DS`: D on contexts / substitutions (DC, DSb), tauC and tau-nat, D~ on types (DT) and elements (De), DT-sub, De-sub (left square of Lemma 67), tauT and hc-tau (horizontal composite = action of τ_Q), Modal := IsEqT τ_Q, Modal-sub, DT-fib | ext; Modal: map | P2.2 |
| S2.4 | (Lemma 12 corrected, Prop 13) `DS.D-eq`: a levelwise equivalence of contexts is sent by D to an internal equivalence | map | P2.2 |
| S2.5 | dropped: Lemma 66 is P2.1, proved in Unit (2-out-of-6) | — | — |
| S2.6 | `DS.isoT`: a map of types with a two-sided inverse (composition n.m = postAt n p m, identity q) is an IsEqT (an iso is an equivalence). Replaces the former premise Prop 17, which is now proved (`duality-levelwise/Prop17.seg`: prop17 from isoT, Lemma 67 and D-eq; prop17-inv from post-eq), with A, B fibrant as extra hypotheses | map | Tiers 4, 5 (through Prop 17) |
| S2.7 | (§6.5) the natural numbers N_DT of PSh(C)_DT over 1.Pr: record `E2.Over.NS` — N, N-fib, N-modal, nE : fibres ≃ ℕ, nE-nat : restriction is the identity on ℕ (the levelwise content of N_DT = D(ΔN) with τ_{ΔN} natural, its components equivalences by Lemma 14) | nE: map (Unit equivalences); nE-nat: ext | Tier 5 |
| S2.8 | `ModPi`: Fib-Pi, Modal-Pi (D-modal fibrant types closed under Π; paper §2.2.2, §5) | map | Tiers 4, 5 |

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
| S3.9 | (ruling 2026-11-10) the inductive types N, List and Expr_G(V) of PSh(C)_DT (V finite) are computed levelwise up to equivalence: at a point of a representable yo x, Expr_G(Fin n) is Expr over alg x, natural in x (u ↦ u·h); and G0's points are syntactic presentations | the equivalence: path; naturality: ext | P3.3 | semantic |
| S3.7 | Propositional truncation Tr of the model, stable under substitution: record `E3.TrS` (Tr, Tr-sub); Unit truncation is `Truncation[l]` (Theory parameters, as Tier 1) | stability: ext | Tier 6 | semantic |
| S3.8 | (Prop 34) `E3.TrS.prop34-l` / `prop34-r`: for A fibrant and D-modal over G, El(G, Tr A) <-> the Unit function giving at each point g of G at x an element of the Unit truncation of the fibre of A at g (reading (A): El(UΓ, ∥UA∥)) | map (both directions) | Tier 6 | semantic |

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
The one such report so far is resolved by the named premise
PCwF.isSetTy (types of the model form a set; S2.1, ruling 2026-11-10),
the homotopical form of judgemental type equality as in two-level type
theory. It constrains instantiation: Ty(Γ) is not a univalent universe;
Sub and El remain arbitrary types.

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
- 2026-11-10 (canonicity-45): Tier 2 checks in `unit/sag/duality-presheaf` (10 modules, 0 failed): T2 records; P2.1 Lemma 66, P2.2 Lemma 67 (context maps), P2.3 Prop 69, P2.4 Lemma 72 proved. P2.5 (Remark 60) and E2 next.
- 2026-11-10 (canonicity-4e): Tier 3 step 1 done: `T3.seg` (record T3,
  statement level: S3.5, S3.6, P3.3–P3.5 with the evaluation clause;
  status of P3.3–P3.5: stated, proof pending). `Core.seg`: the heart of
  Theorem 62 in the model, proved: at every point g of 1.Pr, the fibre
  composite b ↦ G(ev(q_g, b|_{p_O})) equals objIso ∘ brE, hence is an
  equivalence (q_u ∘ p_u⁺ = id read in the model). Remaining for E1:
  P3.6 (the levelwise-equivalence field of the local representation of
  Sp), and the assembly with remark60-eq, Lemma 72, Prop 17, Modal-Pi.
- 2026-11-10 (canonicity-45): **P2.1-P2.5 proved** (Lemma 66, Lemma 67, Prop 69, Lemma 72 with lpt-ext, Remark 60 in both forms) in `unit/sag/duality-presheaf` (12 modules, 0 failed). Premises added on the way, all S2.1: q-pair, pair-eta, Pi-nat, lam-nat, isSetTy (used only through TE.teAny), Site.yoH-eq; S2.8 ModPi. No other coherence field. Next: E2 (Tier 5).
- 2026-11-10 (canonicity-4e): **E1 checked conditionally.**
  `duality-levelwise/E1.seg`, `E1.Over.Thm62[C,S,PI,Dd,MP,T,Md,L58].theorem62
  : IsEqT G0 Br (Π Sp G) (λ ev)`. Premises: T2 (S2.x), T3 (P3.3–P3.5 stated,
  S3.5, S3.6), `Mods` (⟨−⟩ and G D-modal, G and Sp fibrant), and `P58.lw`
  (P3.6, stated, proof pending). Proved here: Core (q_u p_u⁺ = id in the
  model) and the assembly. Next: P3.6 proof (replaces `P58`), then
  P3.3–P3.5 from S3.1–S3.5 (step 3), and E3.
- 2026-11-10 (canonicity-45): **E2 (Theorem 61, Axiom 3) checks conditionally**: `E2[l,k].Over[R,setR].Thm61[C,S,PI,Dd,MP,T,Md,L58,Nn].theorem61 : IsEqT G0 N (Pi G0 Sp N[p]) R6.lamm` in `unit/sag/duality-levelwise/E2.seg` (51 modules, 0 failed; a broken step fails). Premises: those of Theorem 62 (T2, T3, Mods, P58 = P3.6 pending) and S2.7 (`NS`).
- 2026-11-10 (canonicity-45): **E3 (Prop 76 at Sp, Axiom 1) checks conditionally**: `E3[l,k].Over[R,setR].Thm76[C,S,PI,Dd,MP,T,Md,L58,Tt].theorem76 : P76[..].Proj T.G0 T.Sp` (Definition 73 for all substitutions), from `P76.prop76` at a general locally representable fibrant A, with Remark 71 constructed (`P76.R71.rep'`, no premise) (`unit/sag/duality-levelwise/E3.seg`, 76 declarations; a broken step fails). Premises: those of Theorem 62 (P58 = P3.6 pending) and S3.7, S3.8 (`TrS`).
- 2026-11-10 (canonicity-4e): **P3.6 (Prop 58) proved** (`P58.seg`,
  `prop58`), so it is no longer a premise. `SAGPresheaf.seg`,
  `PresheafAxioms[..]`: `duality` (Axiom 2), `n-constant` (Axiom 3),
  `projective` (Axiom 1), all checked, under T2, T3 (S3.5, S3.6, P3.3–P3.5
  stated, proof pending), Mods, NS (S2.7), TrS (S3.7, S3.8). 56 modules,
  0 failed. Remaining: P3.3–P3.5 from S3.1–S3.5 (canonicity-45's
  Transfer.seg is the generic part), and Mods from the model.
- 2026-11-10 (both sessions): P3.3 and P3.4 proved from S3.9 + PModF
  (canonicity-45, `BrFromModel.seg`, 9cf67510). P3.5: record SpF
  (`SpFromModel.seg`: G, Sp as the hom-type of models, ev applies,
  Yoneda for models `globInv`), spE with its equivalence and the
  evaluation clause proved (82aa5b28); spE-nat pending a generic
  onFib-nat lemma. Then T3 is assembled from S39, PModF, SpF and S3.6.
- 2026-11-10 (canonicity-4e): **T3 is no longer a premise.**
  `T3FromModel.seg`: `Build[..].t3 : T3` from S36 (site), S39, PModF,
  SpF; P3.3–P3.5 proved (BrFromModel, SpFromModel, SpNat by
  canonicity-45, 2e9e49cb). `PresheafAxiomsM[C,S,PI,Dd,MP,alg,homAlg,St,
  P,PM,F,Md,Nn,Tt]`: `duality`, `n-constant`, `projective`. Premises now:
  T2 (S2.x incl. isSetTy, lam-nat, S2.8), S36 (S3.6), S39 (S3.9), PModF
  (S3.1/S3.2 fibrewise), SpF (S3.1/S3.5 fibrewise, globInv), Mods (S3.10),
  NS (S2.7), TrS (S3.7, S3.8). 62 modules, 0 failed.

## 6. Handoff (2026-11-10)

**State.** `sag/duality-levelwise/T3FromModel.seg`, `PresheafAxiomsM`:
duality (Thm 62), n-constant (Thm 61), projective (Prop 76) check from
T2, S36, S39, PModF, SpF, Mods, NS, TrS (§5). README.txt there maps
files to jonas.pdf. Check: `./segc sag/duality-levelwise all` from unit/.

**Two sessions.** canonicity-4e coordinates (user ruling: "coordinate
both terminals"); canonicity-45 works. Rules both follow: stop and report
on any coherence (a 2-cell between law-paths) instead of adding fields;
only named premises, each with a DUALITY.md row; each session commits
only its own files/hunks; milestones reported by theorem name; a deliberate
broken step must fail before a milestone is claimed; reading (A) (§4).

**Rulings this day.** Duality-first, then the three axioms; complete-model
endpoint deferred; reading (A); isSetTy; syntactic presentations (S3.9).

**Next (agreed with the user).** Check the paper results taken as
premises:
1. Prop 17 from T2 (canonicity-45): IsEqT closed under composition /
   2-out-of-3 (as fields, or IsEqT made concrete via Swan Id / CwFEq),
   then prop17 / prop17-inv as theorems from Prop 13 (S2.4), modality
   and naturality of tau.
2. The concrete cobar D (Definition 10) on sag-model's cubical base
   (Presheaf.seg, CBase cofibrations incl. [i_k = 0] and unions,
   CLocBoundContr/CTr trivial fibrancy, connections): Lemma 11, Lemma 12
   (the one corrected in doc/jonas-model-review.tex), then Lemma 14 and
   Prop 13; Lemma 54 once PSh(C) is concrete. This checks the paper's
   lemmas in the external (strict) style; linking them to the reading-(A)
   premises remains the §4 obligation.
3. Prop 34 last (needs Theorem 29, Lemmas 31–33).

**Paper remarks found** (to add to doc/jonas-model-review.tex): proof of
Construction 57, first display has s on both sides (should be s, t);
Construction 56 writes the presentation (X, R, s, r) instead of
(X, R, s, t).
- 2026-11-10 (cobar D, sag/cobar): presheaf layer over C (CPshC), R and
  Lemma 9 (CPshR), E and eta, chains of C (Chains, last object indexed),
  D on contexts and types and the unit tau (Cobar) by canonicity-45;
  weights P_n with restriction, faces and Unface (Weights) by canonicity-4e.
  Lemma 12 is being formalised by canonicity-45 from COBAR.md's proof.
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Lemma 12,
  trivial-fibrancy half, PROVED** for the concrete cobar D
  (sag/cobar/Lemma12.seg, 25f40fac): lemma12 al x : ContrOp (D x) (DA x)
  and lemma12U al : UTriv (D G) (D A), from levelwise ContrOp of A only
  (premises: al, the base's CB fields). Negative tests: dropping W3 or
  K.rx-fc fails. Remaining for Lemma 12: the fibrancy half (by the
  paper's reduction to trivial fibrancy via Lemma 11, needs UFib on lines).
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Lemma 12 PROVED
  in the paper's form** for the concrete cobar D: Lemma12F.lemma12F :
  UFib (D G) (D A) from levelwise Fib of A (f604e9a6), via the trivial half,
  CLine's Fill = ContrOp of the strict fibre, and lemma11-lines (Lemma 11
  for lines, as a CMove.Mv transfer). Premises: levelwise Fib of A and the
  base's CB fields. Next: Lemma 14 (lines p, q; ConsId, Weights.ConsP /
  consOne / meetC ready), Prop 13.
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Lemma 14 PROVED**
  for the concrete cobar D (sag/cobar/Lemma14.seg, f81f7f93):
  L14.lemma14 al x : U τ_A is a quasi-inverse equivalence at every x, for A
  levelwise fibrant (ε at the identity chain and weight (1); the paper's
  lines p, q; composition from Lemma 12). Negative test: swapping
  meet-zero / meet-one is rejected. Next: Prop 13.
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Prop 13 PROVED**
  for the concrete cobar D (sag/cobar/Prop13.seg, a0dc0734): if U f is an
  equivalence levelwise (EquivOp, the base's contractible-fibres notion,
  related to internal is-equiv by sag-model S3), then D f is an EquivOp at
  every x (lemma12U on the homotopy fibre, moved along a Psi for fibres).
  Output levelwise. CORRECTION (2026-11-10, pointed out by canonicity-45):
  the paper's internal is-equiv in PSh(C) does NOT follow from the
  levelwise form by propositionality (that gives C-compatibility only up to
  a path, not the strict naturality an element of a presheaf needs); the
  uniform form (CUnif of the fibre ContrOps, from lemma12U's uniformity and
  Psi's C-compatibility) is still owed, for Prop 13 and Corollary 15, and
  for Lemma 16. Negative test:
  breaking fibL-nat is rejected.
  Of the paper results taken as premises, now checked for the concrete D:
  Prop 17 (abstract, from Prop 13), Lemma 9, Lemma 12, Lemma 14, and
  Prop 13 levelwise only (uniform form owed, see the correction above).
  Not checked: Lemma 54, Prop 34.
- 2026-11-10 (canonicity-45): **Corollary 15 PROVED** (sag/cobar/Cor15.seg,
  c79bb0e2): D τ_A is an EquivOp at every x, for A levelwise fibrant
  (Lemma 14 + Lemma 12 + Prop 13; QinvEq: a quasi-inverse between fibrant
  types gives EquivOp, through the CwF of fibrant types). Next: Lemma 16
  (τ_DA an equivalence, the zig-zag on D² A), then Lemma 54.
- Ruling (canonicity-4e, 2026-11-10): the paper's lemmas in their full
  strength, i.e. uniform in C: uniform Prop 13 and Corollary 15, then
  Lemma 16 by the zig-zag with its C-uniformity (needed for S2.4's link).
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Prop 13 and
  Corollary 15 in the internal (uniform) form PROVED** (sag/cobar/Prop13U.seg,
  a86d53d1): prop13U : CUnif of the fibre contractions of D f (the paper's
  element of is-equiv(D f) in PSh(C)); cor15U = prop13U at τ_A. Negative
  test: dropping lemma12U's uniformity fails. Chains.cat (a155dbd4).
  Next: Lemma 16 (uniform zig-zag), then Lemma 54, Prop 34.
- Ruling (canonicity-4e, 2026-11-10) on Lemma 16: (C) now — the C-natural
  zig-zag homotopy K : (D τ_A)[τ_G] ~ τ_DA, the levelwise Lemma 16, and the
  uniform form recorded as conditional on the named statement "uniform
  EquivOp is invariant under a C-natural homotopy" (internal invariance of
  is-equiv in PSh(C)Fib); then (B) — PSh(C)Fib as a CwF instance (C-level
  Σ, Π, Id with uniform fibrancy, S3-style bridge), which discharges that
  statement and gives Lemma 54 its Π. (Lemma 14's ε is not C-natural,
  which is why the paper needs the zig-zag.)
- 2026-11-10 (canonicity-45, checked by canonicity-4e): **Lemma 16,
  ruling (C) form** (sag/cobar/Lemma16.seg, 2e663103): the zig-zag
  homotopy K : (D τ_A)[τ_G] ~ τ_DA at each x (double reading over
  concatenated chains and weights; negative tests on the meet end and on
  cat-junction), and lemma16 x : EquivOp τ_DA levelwise. Owed for the
  uniform form: C-naturality of K (p, q by reindexing; Cat / Inv of
  homotopies uniform in C, which falls under (B)) and the invariance
  statement of the ruling. Next: (B), PSh(C)Fib as a CwF instance.
- 2026-11-10: Lemma 16's lines p, q are natural in C (ea814b0d); K's
  C-naturality modulo the uniformity of Cat / Inv. (B) design approved
  (canonicity-45's note): raw CwF of C-presheaves, ClCwF at UFib, then
  Sigma, Id, the Sigma/Id bridge to EquivOp + CUnif, Pi + NF, then Lemma 54
  and the invariance statement.
- 2026-11-10: (B) stage 1(i) checked (6815674b): CPCwF, the raw CwF of
  C-presheaves (every law the base's at each x), CPshExt (record
  extensionality). Stage 1(ii) (ClCwF at UFib) in progress.
- 2026-11-10: (B) stage 1(ii) checked (4f7ca84c): CFibCwF, the CwF of
  uniformly fibrant C-types (ClCwF at UFib; uniform fibrations are stable
  under C-substitution, module UP). Next: Sigma.
- 2026-11-10: third session canonicity-c2 joins: (B) stage 2(c), Pi for
  C-presheaves (factored as R of the base Pi cut by C-naturality; files
  CPshPi*, CPshNF), then Lemma 54 with ΔK constant in C but a base type
  (cubical set) K, i.e. (Π_ΔK B)_x ≅ base Π_K B_x. canonicity-45 does Sigma,
  Id and the bridge.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): Pi for C-types
  (CPshPi.PiT) and its laws (CPshPiLaws: lam / app / beta / eta, PiIso,
  the shared restriction map resT). Rule for all sessions from now on:
  develop in a private copy of the tree with its own segc server; install
  in sag/cobar only once checked (a nested term had made the shared server
  spin past the 10 s cutoff — a checker observation, kept by canonicity-c2).
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): **Lemma 54
  PROVED** (sag/cobar/Lemma54.seg, 502aaf20): for A whose C-action is a
  bijection on fibres (Cart; ΔK for a base type K is an instance, stable
  under substitution), the fibre of Π_A B at x over γ is in bijection with
  the base Π (A_x, B_x) over γ, i.e. U(Π_A B) ≅ Π_{UA} UB levelwise.
  Premise: fe only. Negative test: dropping cnat-at fails.
  Checker observation (ten-second rule) filed by canonicity-c2:
  scratchpad spinning-CPshPiLaws.seg (+ README).
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): Pi-nat for
  C-types (CPshPiNat.seg, e9c7ebe8): Π is stable under C-substitution.
  Uses V's extensionality (propV-ext, coding CNat by its truth value),
  hence the metatheory's univalence parameter: NOT a new premise, it is
  the existing metatheory premise of sag-model (LEDGER: Unit with
  univalence and funext as segment parameters; V.seg's one use of univ).
- 2026-11-10 (canonicity-c2): raw Π structure complete, CPshPiStr.PiC :
  PiStr on CPCwF (2499e828). The shared uniform-filler lemma is
  canonicity-45's CPshFillU (FillUOf[C].FU, res / fill-C), already drafted;
  canonicity-c2 builds Π's uniform fibrancy on it. NF waits for the C-level Id.
- 2026-11-10 (canonicity-45, verified by canonicity-4e): Σ for C-presheaves
  (CPshSig.PSigC : SigStr on CPCwF) and the shared uniform-filler lemma
  (CPshFillU.FU.res / fill-C), 89993a8c. Checker observation (> 10 s
  nested conversion of the record's coerce spelling) filed in canonicity-45's
  scratchpad (slow-conversion-probe.txt). Next: sigCl, then Id.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): Π's composition
  at each x with NatComp discharged (CPshPiFib + CPshPiFibN, 58395d64),
  from C-uniform fillers of A (FU) and C-uniform compositions of B. Left
  for Π's uniform fibrancy: its C-uniformity (UComp), then the assembly
  piUFib and Π's closure on CFibCwF.
- 2026-11-10 (canonicity-45, verified by canonicity-4e): **(B) stage 2(a)
  Σ complete** (CPshSigFib, 0abb461e): Σ of uniformly fibrant C-types is
  uniformly fibrant; FSigC.SSig is CFibCwF's SigStr. Id (CPshId, C-level
  Yoneda Id) in progress.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): **Π of uniformly
  fibrant C-types is uniformly fibrant** (CPshPiFibF.piUFib, with
  CPshPiFibU.ucomp, b9408810 / acedfb15), no hypothesis left. Remaining
  for Π on CFibCwF: piCl-nat (M3b, the C-level analogue of FibCwF.PiN.law).
  Second checker observation (rdC at PiT overran 10 s; generic form
  instant) filed by canonicity-c2.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): **(B) stage 2(c)
  Π complete on CFibCwF** (CPshPiFibS / CPshPiFibC, 62293935):
  FPiC.SPi : PiStr of CFibCwF (piCl = piUFib, piCl-nat = PNat.law). No
  hypothesis left; premises fe, univ via V's extensionality. Next: NF
  (canonicity-c2), Id fibrancy + J (canonicity-45), then the bridge.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): NF for C-types,
  raw form (CPshNF.NFC.nf, 7ef00e6b), with the generic LineYC (a natural
  line field of a C-type is an element of its Id). Fibrant instance waits
  for CPshIdJ.
- 2026-11-10 (canonicity-45, verified by canonicity-4e): **Id's uniform
  fibrancy complete** (CPshPathU, CPshCoreIdU, CPshIdFibM/T/, 559e22ee:
  idCl and its substitution law) and **JNatT** (CPshJNatT, a8462853: J
  commutes with any commuting map of J-data, generic). Next: the IdJStr
  instance on CFibCwF (CPshIdJ). Bridge (canonicity-c2): C1, U-Rel and the
  fibres (II-a) done; C2 next.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): bridge S3b_C at
  the raw level (CPshContr C1 / C2, CPshURel, CPshFibMaps, CPshFibC). Ruling
  on the converse S3a_C: Option C, a new base lemma "a ContrOp of
  Σ_Y Path gives a ContrOp of Σ_Y YonedaId" (extend the path, take the sieve
  {f in Q | id in the side's Id-sieve at f}, a dependent conjunction); this
  is a new argument, not the base's FibS3.A, and shows the latter does not
  need the path fillers.
- 2026-11-10 (canonicity-c2, verified by canonicity-4e): **bridge, both
  directions at the raw level** (CPshIdExt: the new lemma contrI / contrFV;
  CPshFibC.SA.utFV), no J used. Remaining: packaging on CFibCwF and the
  Lemma 16 invariance, after canonicity-45's PIdJ. Meanwhile canonicity-c2
  plans Prop 34 (design note only).
- 2026-11-11 user decision on Prop 34 (after canonicity-c2's plan in
  COBAR.md, be548901): P3 then P1. First finish what Prop 34 needs anyway:
  the bridge's packaging, Lemma 16's invariance (uniform form), and
  Theorem 29 (D a descent data operation, incl. D stable under
  C-substitution). Then Prop 34 conditional on ONE base-level premise (a
  record of the base truncation's interface), replacing S3.7 / S3.8.
  Building the base truncation itself (P2) is not undertaken.
- 2026-11-11 (canonicity-c2, verified by canonicity-4e): D on
  substitutions and elements, its functoriality and τ-naturality, and D on
  types stable under C-substitution (CPshDSub / CPshDSubT: DSb, DSb-id,
  DSb-o, tau-nat, DEl, DT-sub, DAC-sub). Toward Theorem 29.
- 2026-11-11 (canonicity-45, verified by canonicity-4e): **(B) stage 2(b)
  Id complete**: CPshIdJ4.PIdJ : SwanId IdJStr on CFibCwF, all eight fields,
  no parameters (3eeba328). So CFibCwF has Σ, Π, Id (Swan, with J). Rule
  learnt: module-instance arguments must be spelled literally.
- 2026-11-11: Theorem 29 design approved (COBAR.md, 8508d980,
  canonicity-45): part (A) M1-M7 (D-bar on CFibCwF, desc1 from Cor15U,
  desc2 from the uniform Lemma 16), lex operation taken directly. Part (B)
  (instantiating T2's DS record from the concrete D: the start of the §4
  link) deferred for a user decision, together with Prop 34 (P1).
  Bridge packaging (III) by canonicity-c2 approved; Lemma 16's homotopy to
  be rebuilt internally (LineYC on the C-natural lines p, q, then PIdJ's
  transitivity / symmetry), removing the Cat / Inv uniformity item.
- 2026-11-11 (canonicity-c2, verified by canonicity-4e): NF instance on
  CFibCwF (b2467982); **bridge packaged** (574f6f29: CPshContrC, CPshFvC,
  CPshFvC2, CPshS3C: S3a / S3b on CFibCwF in Prop13U's shape); **invariance**
  (CwFKrInv: Kr invariant under Id / homotopy; CPshMapC: CMap <-> CEl;
  CPshInvC: Inv, InvM, Zig). Attribution note: the invariance files
  (CwFKrInv, CPshMapC, CPshInvC, the CPshFvC refactor, c2's All.seg /
  COBAR.md hunks) were committed inside canonicity-4e's commit 376d6c93
  (titled "doc/duality-presheaf: base ring k"), which swept in c2's staged
  files; the content is c2's and checked. Lemma 16 uniform: canonicity-45
  instantiates Zig with the C-natural lines (desc2).
- 2026-11-11 user decision: after Theorem 29 part (A), do part (B)
  (instantiate T2's DS record from the concrete D: De-sub, hc-tau,
  Modal-sub, D-eq, isoT, restr-eq, post-eq), then Prop 34 conditional on a
  base truncation interface.
- 2026-11-11 FINDING (canonicity-c2, ruled by canonicity-4e): T2's record
  DS has NO Unit instance with El := CEl (the concrete external model).
  T2 is read internally (El a Unit type whose Id is a path); in the
  concrete model global elements form a SET with strict equality, so a
  field such as post-eq ("an internal equivalence induces an equivalence
  on elements") becomes "a bijection", which is false (a contractible
  fibrant type with two strictly different points). The same holds for
  every field whose conclusion is an isEquiv or an Id of El-types (or of
  points, e.g. LocRep's levelwise-equivalence field) that holds only up to
  homotopy. This is exactly obligation (i) of §4: the link from the
  concrete model to the duality proof is an INTERPRETATION of the internal
  reading in cubical sets, not a record instance. Part (B) is therefore
  reinterpreted (ruling O1): prove the concrete counterparts — strict
  fields (isoT, Modal-sub, De-sub, hc-tau) as stated, the homotopical ones
  in setoid form (post-eq-h, restr-eq-h: equivalences of (El, internal Id),
  uniform in C) from the S3 bridge.
- 2026-11-11 (canonicity-45): Theorem 29 (A): M1/M2 (CPshDT: Dbar,
  Dbar-sub, Dbar-fib, eta, record DescentOp on the RAW CwF with fibrancy as
  a class), M4 (subCMap), M5 (subUTriv, subEqU), desc1 checking; M6 (Lemma
  16 via LineYC + Zig) and M7 remain. KNOWN GAP (recorded on purpose): the
  paper's Lemma 12 is natural in Γ; the stability of the produced fibration
  structures under substitution on the nose is not proved (not used
  downstream), which is why the record sits on the raw CwF.
- 2026-11-11 user ruling: part (B) STOPPED (it cannot instantiate T2, see
  the setoid finding above, so it is not needed). Remaining: Theorem 29
  part (A) (canonicity-45: M6 uniform Lemma 16, M7; canonicity-c2: η-nat),
  then Prop 34 conditional on one base truncation-interface premise
  (canonicity-c2: design note first).
- 2026-11-11 USER DECISION: C must be internal to the base, as in jonas.pdf
  Assumption 2 (a functor from cubes to Cat; Construction 39's C of fp
  models in h-sets varies over cubes). sag/cobar so far is the constant-C
  (Coquand-Ruch-Sattler) case. Redo the presheaf layer over the
  Grothendieck construction ∫C (C0 a base presheaf, C1 a base family over
  C0 x C0, strict laws), and ONLY what checking the SAG axioms needs
  (duality, constancy of N, projectivity): D, Lemmas 12, 14, 16, Prop 13,
  Theorem 29, Lemma 54, Prop 34, and the CwF structure they use. The
  constant-C results stay in the tree as the CRS case.
- 2026-11-11 USER REFOCUS: no need to check that PSh(∫C)_D is a full model
  of type theory. Goal: define the generic k-algebra G concretely over ∫C
  and check the SAG axioms for it (duality first, then N, projectivity),
  using only what these statements need (the concrete presheaves G, <u>,
  Sp, G^Sp, their modality, levelwise => internal equivalence for modal
  types). Design note (canonicity-45 with c2) rewritten as this minimal
  route.
- 2026-11-11 CORRECTION (errata2.pdf, Coquand-Höfer-Sattler erratum to the
  SAG paper): the argument "C = C_const (constant fp k-algebras) for a
  fixed ring k" (canonicity-4e, -45, -c2) is WRONG in general. Δ(L[X]/q),
  the constant presheaf on a metatheory set quotient, need not be the h-set
  quotient (ΔL)[X]/q of the cubical model (levelwise problem); strict
  coherence is a second problem, solved by the cobar relativisation
  (erratum Lemma 2.1). Constant C + D works when presented algebras have
  normal forms with derivations (erratum Lemma 2.2; k = Z, a discrete field
  or fp over Z, by constructive Gröbner bases). The general case is
  jonas.pdf's internal C, which avoids metatheory set quotients. Route
  choice pending with the user.
- 2026-11-11 USER DECISION: route R2 (jonas.pdf's internal C, the general
  case), to check jonas.pdf's main results. h-set quotients in the base are
  to be CONSTRUCTED from propositional truncation (SAG.pdf §8.3, core's
  CTrunc*, no HIT) and replacement / a universe of propositions
  (Voevodsky's impredicative quotient), not assumed. First steps:
  canonicity-c2 builds the base truncation (BaseTrunc a-d);
  canonicity-45 revises INTERNAL-C.md for R2 with no premise record.
- 2026-11-11: user approved doc/sag-presheaf-plan (7afb66c0) and asked
  canonicity-4e to proceed AUTONOMOUSLY. Simplified plan
  sag/cobar/SIMPLIFIED.md (2f0fc081): axioms as propositions + Key Lemma
  (no Prop 13 / 17 / Theorem 29), quotient-free duality (no <u>_{T/G}, no
  second universe step), projectivity at a fixed context, iterated
  presentations as objects of C. Under critique by canonicity-45 / -c2.
- 2026-11-11 (canonicity-c2, verified): R2 step 1, base truncation DONE
  (95d00831): CTruncCwF.TrOf: Tr0 fibrant STy (CTruncFib.truncFib via the
  pushforward CTruncPush*), unit, proposition (isContr form), elimination
  into fibrant propositions with beta. SAG.pdf §8.3, no HIT, no strict
  substitution stability (not needed: projectivity at a fixed context).
- 2026-11-11 (canonicity-45, verified): pilot done (43160f98, ed1f393a:
  CCyl, CConst constant types fibrant, CPilotRing); factor 2.5, step 2 now
  1,500-2,500 lines. RULING (canonicity-4e): the congruence of A_x must be
  the BASE truncation of proof-relevant derivations, Tr0(Δ Der_x(t, u)),
  not Δ of the metatheory proposition ||Der||: eliminating a metatheory
  truncation into El(G, Id x y) (a set, not a Unit proposition) is the
  erratum's levelwise problem.
- 2026-11-11 CONSTRAINT (canonicity-c2): without strict substitution
  stability, the base truncation Tr0_G A has no code in U over a varying
  context. Allowed: codes of CLOSED truncations (constant families, e.g. the
  congruence Tr0_1(Δ Proof_x(t, u)) of A_x, by closedCode); truncations
  never put in a universe (the axioms' outer truncations, the image in Q).
  If a coded truncation over a varying context is ever needed, the dropped
  strict stability (700-1,100 lines) must be reconsidered.
- 2026-11-11 RULING (canonicity-4e): propositional extensionality for the
  base universe (needed by Prop_U and the Voevodsky quotient) enters as ONE
  module parameter PropExt, discharged generically from the internal
  univalence UaContr (CwFUaEq); the remaining link is the base instance of
  UaContr (S4, LEDGER row 7, unfinished). To be finished so the axioms carry
  no hypothesis; canonicity-c2 measures S4 after Q.
- 2026-11-11 (canonicity-45, verified): the cobar construction D over the
  total site of an INTERNAL category (4554edd5): CIntCat (split displayed
  internal category), CVert, CTotCat, CobarI (D on contexts, tau natural,
  D on maps), CobarIT (D on types). Step 4 at 1,770 lines. canonicity-c2
  switched to GrothCB (the base structure at the total site), which Lemma
  12's trivial-fibration half needs; then SliceCB, then the rest of Q.
- 2026-11-11 FINDING (canonicity-45, confirmed): C has no STRICT terminal
  object (maps out of the initial algebra are unique only up to internal
  paths), so the interval of the total site is not representable; in
  jonas.pdf it is the presheaf (J, y) |-> Hom(J, Iv), only cylinders being
  representable. RULING in principle: generalise CB to an interval
  presheaf (option iii); core uses the interval object in 121 of 282 files,
  so canonicity-c2 measures the closure needed at the total site first.
- 2026-11-11 (canonicity-c2 measurement): core uses the interval object
  ONLY as a codomain (786/786 occurrences are maps into Iv), so the
  interval-presheaf generalisation of CB is a mechanical rewrite (49 member
  files + CBase), done first in a private copy, then installed in place.
  RULING: at the total site identity types are Path types (generic), not
  Swan Id (whose poset version needs the conjunction cofibration); only the
  packaged pieces actually consumed at ∫C are re-parametrised.
- 2026-11-11 USER DECISION: the interval-presheaf rewrite of CB is installed
  in unit/core IN PLACE (this change only; core otherwise read-only).
  Rewrite green in canonicity-c2's private copy (345 modules, 0 failed, no
  file over 10 s; existing instances unchanged in meaning). GrothCB then
  uses no terminal object. Swan's Id is available at the total site (the
  DConj record through the projection, 45 lines), so the strict-J toolkit
  ports; the Fib* / PosId* layer (17 files) is base-generic in substance and
  becomes a segment FB over CB with shims.
- 2026-11-11 INSTALLED (c2, 1fd0fe1e): the interval of CB is a presheaf IvP
  (user-approved in-place rewrite of core; 62 paths). Verified by 4e: core
  all 282/0; sag/cobar CGrothBase, CPshIdFibT, CPshIdFibT2 (5.20 s), Lemma14
  ok. c2 ran sag-model/All 205/0 and sag/cobar/All 356/0 (slowest CPshFibC
  8.8 s). sag-model's .seg files are not under git: the PosFull / CPosInst
  shim edits are working-tree only (originals in c2's scratchpad backup-iv/);
  versioning sag-model is a user decision. Quotient since: elimP (e8b45173),
  CwFUnpk (ad156e9b), relV-pt (c570073f). Next (c2): FB segment in sag/cobar,
  total-site instance, then Q's elim into h-sets, set-ness, elim2.
- 2026-11-11 sag-model put under git (b6f6c6c2, user-approved; 205/0).
- 2026-11-11 FB segment (c2, 8d96c7be): CFibSeg[a].FB over CB's fields + DConj;
  18 G*.seg generated from the poset files (sag/cobar/tools/mkseg.py, ivrw.py;
  16 unchanged proofs, 4 hand patches lands-pre in GCLocBound*). Total site:
  GrothOf[C].FT gives fibCwF-T, fibPi-T, fibSig-T, Swan Id with strict J
  fibId-T, funext nf-T, contr-T, for any internal C. Universe, univalence,
  truncation NOT at the total site (transported by R). Verified by 4e: 20/0,
  14.00 s. Poset files kept as source (no shims). Next (c2): item 5 (R, Tr :=
  R Tr0 U, KL), plan first; then Q's elim into h-sets, set-ness, elim2.
- 2026-11-11 LEVELWISE ruling (4e, after 45's objection): levelwise fibrancy is
  Höfer's (fibrancy over the discrete C0 = GrothOf[DiscOf[C].disc]), not
  fibrancy over the Σ_{C0}-context (lines there may move the object; jonas.pdf
  §5.1, Remark 5.9 of [32]). Theorem 21 (Assumption 4) bridges the two but is
  NOT used: instead the 37 truncation files are generated generically in FB
  (c2, 20-40 lands-pre patches) and instantiated at the discrete site. Theorem
  21 serves only T_C (§5), outside our route. Item 5 order: generic Tr0, CTotU
  (restriction along 45's functor ∫C0 → ∫C), CTotR + adjunction, fibrancy,
  CTotTr, KL.
- 2026-11-11 Generic truncation (c2, 5a02d28c): the 37 truncation files
  generated in FB (28 unchanged, 26 lands-pre patches in tools/patches.json).
  CGrothBase has Tr0-T, contrTr-T at the total site of any IC. Verified by 4e:
  57 modules (CFibSeg, CGrothBase, 18 G-interface, 37 GCTrunc*) 57/0, 16.76 s.
  Tr stays R Tr0 U (ruling); Tr0-T -> R Tr0 U comparison available if needed.
- 2026-11-11 U and R (c2): CRestr (fddd8e1a, restriction along F : Cs -> Ds)
  and CRan (baacecc8, right Kan extension, strict adjunction on elements toR /
  ofR / of-to / to-of), generic in F. Verified by 4e: 2/0. Next (c2): fibrancy
  of R B (ContrOp half first), needs 45's CDisc committed.
- 2026-11-11 CDisc (45, f617709b): discrete C0 as an IC, functor fn into C's
  total category (fnId / fnComp), resC / resS; IC without terminal objects;
  CCyl over IvP. Verified by 4e: CDisc CIntCat CVert CCyl CConstLam CConst
  6/0. Batch overruns of CPshFvC2, CPshInvC, CTruncAtBase under load ~34 (45
  re-running). Next (45): CRelResp, CClsEqC (derivations give equal classes).
- 2026-11-11 (45, e12506ca) CClsEqC.clsEqC: a derivation t ~ t' gives Id-equal
  classes in A_x; CRelResp.rsRel: Rel gives Id of evaluations in an h-set ring.
  Verified by 4e: 2/0 (CClsEqC 4.37 s). GFibIdCen 6 s at load 5, 14-15 s at
  load 30+: load, not a defect; no split for now. Next (45): CAlgX (ring
  structure of A_x, elim2 / set-ness as parameters), then HRing[nil], C's maps.
- 2026-11-11 (c2) CTotR (e3730cbd): Lemma 9 for internal C, R of a levelwise
  ContrOp is a ContrOp (contrR); elimP-at / elimP-el (24a14799); incS-sec /
  atCls (846c9add). Verified by 4e: CTotR, CwFQuotElimP 2/0. Lines do NOT
  commute strictly with R (only a currying iso); Fib half by componentwise
  transfer of Comp e e' along rho (only the "to" direction), 400-500 lines.
- 2026-11-11 CORRECTION (45, ruling 4e): C0 is NOT constant. Def 48 / Prop 58
  need x.γ for γ a presentation whose relations are STAGE elements of A_x[Y]
  (elements of a base quotient, only merely classes of terms). Ruling: objects
  = iterated presentations with internal relations, by recursion on length:
  C0_{r+1} = Σ (x : C0_r) Σ (n,m) (Fin m -> A_x[Y_1..Y_n])^2; x.u =
  concatenation (strict). A_x := Q(ΔTerm_{N(x)}, R_x), R_x = truncated
  derivation trees whose equation leaves carry "t' ∈ s" (membership in a
  Voevodsky class: small), so A_x stays at a+1; C0 at a+2 (to be checked
  against IC). Plan note (B4: "~_x a set of the metatheory") to be corrected.
  45 sends the recursion's shape before CMorX.
- 2026-11-11 (45, 83b6a374) ring laws of A_x at all elements (CAlgFun, CAlgLaw,
  CAlgLaws, CAlgLaws3). Verified by 4e: 4/0, 10.91 s. Consequences of the
  non-constant C0: (2) vertical level IC[a, l], l = a+ (C0, C1 at a+; ~18
  files re-levelled, go); (3a) A_x and its ring structure over a context with
  x : El G C0 (go); (3b) codes for truncations over a context (asked of c2).
  Object shape: 45's layered recursion vs 4e's flat form (predicate pairs
  S, T on Term with a propositional validity field; x.u = concatenation),
  45 to compare.
- 2026-11-11 (c2) R preserves levelwise fibrations: CTotRFib..CTotRFib8
  (34106a20 .. 252da550, ~1,050 lines), fibR / compR. Verified by 4e: 8/0.
  (c2's 9745c32b dropped the CAlg* imports of All.seg; restored e0f6071c.)
  OPEN (blocks the object shape): the relations R^{<j} and Valid need codes
  (Prop_U) for truncations of small families over contexts at level a+; c2
  says its truncation over such contexts is not small. Asked c2: is Tr0 over
  representables strictly stable along cube maps (=> code former tr : U -> U)?
  45 writes CObj / CRelI with the code of the truncation as a parameter.
  c2's site files move to the vertical level l after CTotTr.
- 2026-11-11 RULING (4e, on 45's proposal; user may reverse): Prop 58 in the
  MERELY form (||local representation|| at each (x, γ)). All uses (Lemma 59 /
  72, Remark 60 in Thms 61, 62, Prop 76) have propositional conclusions, so the
  mere x.γ is eliminated inside the base. C0 = constant syntactic
  presentations, C1 = internal Construction-39 maps between the internal
  quotients A_x; step 2 stands; CObj / CRelI and the layered/flat objects of
  the previous two entries are DROPPED. Homs of IC at level l = a+.
  Shelved, for Höfer's full Def 48: c2's Route 1 (location-free trees as in
  SAG.pdf §8.3, bridge to core's CTrunc, code former tr : U -> U; 1,100-1,500
  lines). Note: core's CTrunc stores context locations in its trees, so it is
  neither small over large contexts nor strictly stable; SAG.pdf's is both.
- 2026-11-11 Vertical level in: 45's 03bef1e8 (CIntCat[a, vl], cobar layer at
  [a, vl, l], base codes embedded) and c2's 0d43c526 (site files at vl);
  shared run 431/0. 45's 391ba9a9: CDisc.Fact / Cancel / Ini (factorisation
  of total maps, for U preserving fibrations). Verified by 4e: 10 key modules
  10/0. Next (45): CMorX, IC instance, universal map of A_x, Prop 58 (merely).
- 2026-11-11 (c2) U preserves fibrations: CTotUExt .. CTotUFib4 (8bbd6371 ..
  ab20a0e4, 625 lines); lines commute with U (rho is a bijection, via 45's
  CDisc factorisation). Verified by 4e: 5/0. Next (c2): CTotTr (Tr := R Tr0 U
  fibrant, unit, proposition; contraction over G.Tr A via the counit).
- 2026-11-11 (c2, 0cbcbc44) the model's truncation: CTotTr.Tr = R Tr0 U as a
  type of fibCwF-T, contrTr (a proposition, via the seeded extension operation
  transferred through R, CTotRSeed), inc, sec (levelwise element -> element).
  Verified by 4e: 2/0. Next (c2, (vi)): (a) r and D-modality of Tr A; (b) KL;
  (c) Prop 34 right-to-left as the eliminator into D-modal propositions.
- 2026-11-11 Lemma 12 at the total site moved to c2 (45's queue is the
  critical path). Interface: L12T[C, G, A].lemma12 : levelwise ContrOp (U G)
  (U A) at GrothOf[disc] -> ContrOp (D G) (D A) at the total site. Port NOT
  mechanical (restriction moves objects and chains); c2's estimate for the
  trivial half 2,000-2,500 lines; reports at level 0, the step, lemma12.
  Lemma 12 is needed for: G fibrant, D (Tr A) a proposition (modality), KL.
- 2026-11-11 Lemma 12 at the total site, full size (c2): fibration half needs
  Lemma 11 for lines at the total site (port of Lemma11L, 900-1,300 lines) +
  CMove.Mv + fromFill (100-150); total both halves 3,000-3,800 lines, inside
  the plan's step 4 (6,700-8,900). Accepted. First slice lemma CTotL12ch
  checked privately.
- 2026-11-11 Lemma 12 at the total site, level 0 complete (c2, f9f7deb1;
  CTotL12ch, CTotL12a-f, ~1,000 lines, no 2-cell). Verified by 4e: 7/0.
  Next: face pieces, Join, step; uniformity; lemma12.
- 2026-11-11 (45, c31c6301) THE INTERNAL CATEGORY C: CPresCode (objects:
  presentations, coded), CMorX (Höfer's maps A_s -> A_t at each stage, data
  for add, mul, phi r; strict composition), CMorXC.CatOf.IC : CIntCat[a, a+].IC
  (C = algebras^op; res = id, cart = id on constant objects). Verified by 4e:
  3/0. addO / mulO (A_x's operations) are parameters until c2's closed
  eliminator with beta. Next (45): Lemma 14 / Prop 13 interfaces against
  L12T; Prop 58 statement (merely).
- 2026-11-11 Lemma 12 at the total site, the step complete (c2, 56fb71d3;
  CTotL12g-l: face pieces, compatibilities, Join, step, build : (n) -> Up n;
  ~2,000 lines, no 2-cell). Verified by 4e: 13 CTotL12* modules 13/0.
  Remaining trivial half: assembly, kside, kunif, the ContrOp record.
- 2026-11-11 LEMMA 12 AT THE TOTAL SITE, TRIVIAL HALF DONE (c2, 603a3d9d):
  CTotL12n.lemma12 : levelwise ContrOp (U G)(U A) -> ContrOp (D G)(D A), any
  internal C; 15 files, 2,026 lines, no 2-cell. Verified by 4e: 15/0. Next
  (c2): fibration half (Lemma 11 for lines at the total site, Mv, fromFill;
  1,000-1,450), then tau on types, r, D-modality of Tr, KL, eliminator.
  45 starts Lemma 14 / Prop 13 against it.
- 2026-11-11 Queue (45 + c2, agreed): tau on types -> 45 (first part of
  Lemma 14 at the total site, CTotL14*); c2: lemma12F + generic CTotPsi
  (read families over total maps at cartesian lifts), which 45's Prop 13 Psi
  instantiates. 45 does Lemma 14 with lemma12F as a parameter first.
- 2026-11-11 LEMMA 12 AT THE TOTAL SITE COMPLETE (c2): fibration half
  49c42ccf (CTotL12Fib, CTotL12Fib2.lemma12F, CTotLvl..4, Lemma 11 for lines
  CTotPsi..22); trivial half 603a3d9d. Verified by 4e: CTotL12Fib,
  CTotL12Fib2, CTotL12n ok (the CTotPsi* / CTotLvl* batch queued behind the
  server). LEMMA 14 AT THE TOTAL SITE (45): CTotL14a-h, lemma14 at lemma12F, no
  parameter left (h committing). 45 also: CBridge, CAppRd (d0771b0d), CSemOp,
  CSubst, CFreeMaps (f83b6ea0), CGen (yo F1, G, evG), CDProd (D on products,
  N_D) - verified 4e (with CMorX, CTotL14a-c) 14/0. Next: c2 QE1 (elim1/beta,
  setQ, elim2, ElimP3, ElimP1, setQi, setW), then r, modality, KL; 45 the
  data of the free maps, bridge instances, comparison, G's operations.
- 2026-11-11 (45, e3f9300c) Lemma 14 at the total site complete (CTotL14h);
  Höfer data of closed maps (CQCtx, CHomData, CMapsC/C2/I): I1, I2, AddF,
  MulF, p_u as morphisms of C; CCmp: strict comparison yo F2 -> yo F1 x yo F1.
  In check: CGops (G's + and * with Prop 13's inverse as parameter).
  RULING (d): the inverse of yo(x.u) -> yo(x).Sp(u) via "injective + merely
  surjective between sets => equivalence": choose term representatives
  internally (Tr0 from surj), closed substitution maps packed over ΔTerm^n,
  injectivity by ElimP; gives the levelwise equivalence OUTRIGHT (no
  elimination over non-closed contexts needed).
- 2026-11-11 (45) CInjSurj.contrFib (contractible fibres from propositional +
  merely inhabited, any context). (d) scoped at several days ((i)-(v): the
  tautological algebra over G0, yo(x) at G0, Sp(u), forward map, inverse).
  ORDER (4e): Prop 13 at the total site first (critical for G's operations
  and laws, Cor 15, Lemma 16, Lemma 59), then (d). G0's fibrant CwF =
  GrothOf[disc].FT.
- 2026-11-11 Prop 13 at the total site (45): c0b4795c (D on maps), CTotP13b-c
  in check. Psi on HFib: specialised copy (constant base line), not a
  generic Psi12-22 (would restate ~2,500 lines); accepted by 4e. c2's QE1
  part 1 e5cf7c12 (setQi, setQ, setW).
- 2026-11-11 PROP 13 AT THE TOTAL SITE (45): CTotP13o.prop13 : levelwise
  EquivOp (U f) -> EquivOp (D f), any f between types over any total context;
  d committed 286264ac, e-o (Psi on HFib, ~900 lines) in shared check.
  Next (45): discharge CGops's inv with prop13, then (d)(i)-(v).
- 2026-11-11 Using Prop 13 for G's operations needs (A) identity EquivOp,
  (B) F2 = F1 + F1 in C (levelwise inverse of the comparison), (C) contexts
  as types over 1, (D) the inverse map out of an EquivOp. With (C) the type
  form of Prop 13 suffices everywhere (G's ops, Lemma 59, Cor 15 / Lemma 16).
  Split: c2 does (C), (A) right after QE1 (before r / modality / KL); 45 does
  (D) (CEqCen, checks privately), (B), inv, then (d)(i)-(v).
- 2026-11-11 (B) re-estimated 500-800 lines (45): universal property of the
  free algebras at every stage (evaluation by elim1, Höfer data by ElimP3 /
  ElimP1, uniqueness by term induction on classes). 4e: state it for F_n,
  n metatheoretic, if cheap (gives F0, F1, F2 and (d)'s substitution maps).
- 2026-11-11 Prop 13 committed (45, 02e9b8ce; shared 530/0). Verified by 4e:
  CTotP13* 15/0, 17.84 s. 45 now: universal property of F_n (valuations Fin n
  -> A_x, Höfer data, uniqueness).
- 2026-11-11 FINDING (45): yo F2 -> yo F1 x yo F1 is NOT a strict bijection
  (maps of C out of quotients agree only up to Id; fibres of Q not discrete),
  so idEq + moveEq cannot give its EquivOp. RULING (4e): as in Höfer's Lemma
  43, prove it a levelwise equivalence INTERNALLY in the fibrant CwF of the
  levelwise site (tautological algebra A over G0; uniqueness by elimP + funext,
  existence by elim2; data propositional since A is a set), then bridge
  internal isContr -> EquivOp (FibHt / FibContr layer). Same for Lemma 59.
  (A) idEq dropped. 45's order: (d)(i), this, (d)(ii)-(v).
- 2026-11-11 QUOTIENT ELIMINATORS COMPLETE (c2, QE1): set-ness (Hedberg-Kraus,
  e5cf7c12), elimP1 (2dfbc935), elim1 / beta by unique choice (2e0fb362), Fun
  A B a set (60647d67), elim2 / beta (e45484d1), ext1 / ext2 (0ffd9f4b),
  elimP3 (76816711). Parameters: pe, NF, the truncation instance only.
  Verified by 4e: 19 modules 19/0, 6.51 s. (A) idEq dropped. Next (c2): (C)
  contexts as types over 1, then r, D-modality of Tr, KL.
- 2026-11-11 (45) internal Hom for the comparison: CHomT1-3 (private, check):
  HomT = Σ (h : Fun Q_s Q_t) data, fibrant by construction. Remaining for G's
  operations: (P3) HomT(J) = CMorX's M J, the inverse, the two homotopies,
  QinvEq -> EquivOp, (P1) componentwise to G0: 1,200-1,800 lines, several
  days. Then (d) for Lemma 59 / Prop 58.
- 2026-11-11 (c2) (C) contexts as types over 1 (d79bb994, CTotCtxTy);
  elimPH / ext1H for 45 (fed7f506); r : (D (R B))[tau] -> R B with r . tauA =
  id (3494f167, CTotRr). Verification queued (server busy). Next (c2):
  D-modality of Tr, KL (form (b)), eliminator (c).
- 2026-11-11 KEY LEMMA (c2, acd51e87): CTotKL.sec : a section of P over G from
  a natural map (D P)[tau] -> P and a levelwise ContrOp of U P (Lemma 12
  trivial half, section of a ContrOp, tau pullback). Next (c2): D preserves
  propositions / h-sets, modality of Tr, KL from a levelwise element, (c).
- 2026-11-11 D PRESERVES PROPOSITIONS (c2, 338c0e4f; CwFPropNoU, CTotDProp1-3):
  isPropD from a levelwise ContrOp of A over G.A (Lemma 12 trivial half moved
  along Pair.phi). Verified by 4e: 4/0. h-sets: needs D(Id_A) vs Id_{D A}
  comparison (after the modality of Tr and (c)).
- 2026-11-11 (c2) CTotDProp4 (77520e5f: D preserves propositions from an
  internal levelwise isProp); CTotKL2 (b25fc427: KL from a levelwise element).
  Verified by 4e. Modality of Tr needs "U preserves propositions" (or U (R B)
  levelwise prop): after (c).
- 2026-11-11 (c2) U preserves propositions (c067a650, CTotUProp1-3) and THE
  MODALITY OF Tr (48abba21, CTotTrMod.modal : Equiv Tr (D Tr)[tau], from both
  being propositions + r + tau). Verified by 4e: 4/0. Next (c2): (c), h-sets.
- 2026-11-11 (45) (P3) done: HomT(I) <-> CMorX's M I (beta, alpha, both round
  trips, naturality), the cart for moveEq; beta committed 89a4e066 (shared
  562/0), CHomT9-16 in check / private. LESSONS: (1) Swan's Id here is the
  Yoneda Id (PosIdY.IdYT), whose fibres depend on the context's action, so
  Id types over different contexts never convert (10 s overruns): build both
  sides as substitutions of ONE Id type. (2) Data as one Π over a closed Σ:
  the Σ's action is CMorX's restriction on the nose. Next (45): the inverse
  from CFreeEval.E, homotopies via elimPH / ext1H, QinvEq, (P1).
- 2026-11-11 (45, fdc5d39e) HomT <-> CMorX codes complete (alpha, round trips;
  shared 571/0). Remaining for the comparison's EquivOp: (U) uniqueness and
  (E) existence, internal algebra in the poset fibrant CwF -> assigned to c2
  after (c) and the h-set comparison. 45: plumbing (moveEq to codes, (P1),
  hookup into Prop 13 / CGops) with the EquivOp as parameter, then (d).
- 2026-11-11 (c2) (c) the eliminator of Tr into D-modal propositions
  (CTotElim5.elim; levelwise prop-ness derived by UP3), checks, commit after
  the shared run. h-sets: only G and N_D needed (not the general "D preserves
  h-sets"); c2 to compare a specific route with the path half of Lemma 11.
- 2026-11-11 h-sets: general route via PATH types accepted (isSet (D A) from
  isProp Path_{D A}, Lemma 11 for lines packaged as a move, U of paths, DP4;
  3-4 files, +1 Id ~ Path bridge if missing). Specific route was not shorter.
- 2026-11-11 THE ELIMINATOR OF Tr INTO D-MODAL PROPOSITIONS (c2, b0f84058,
  CTotElim1-5): Prop 34 right-to-left. Verified by 4e: 5/0. h-sets route
  adjusted: Hedberg-Kraus (CwFHed4) with R = D(Id_A) pulled back (a
  proposition by DP4, reflexive, one map R -> Id_{D A}); D(Id_A) and Id_{D A}
  are not isomorphic. 3-4 files.
- 2026-11-11 (45) plumbing for G's operations: (P1) CCopy/2/3 (0d621fab,
  shared 582/0: G0 EquivOp from one per presentation copy), CCmpY..4 in check:
  D cmp an equivalence (Prop 13), inv by CEqCen, G's + and * as constructions
  (CCmpY4.Ops.GO). Open inputs (c2): per y, al, eqal (from (K) via S3b), commH.
  Order (45): (d), Lemma 59, Cor 15 / Lemma 16 at yo F1, G's laws, 0 / 1.
- 2026-11-11 RULING (4e) on (d): per copy, internal, with the tautological
  algebra: HomT(x.u, y) ≃ Σ (h : HomT(x, y)) Sol_h(u), Sol_h(u) := Σ (v : Fun
  (ΔFin m) Q_y) Π_j Id (ev_{u_j}(h∘g, v)) 0, ev_t by METATHEORY recursion on the
  syntactic term t (u constant; no eliminator, any arity). Inverse by
  injective (ElimP1 + term induction through the data) + merely surjective
  (Tr0-chosen representatives, closed substitution packed over ΔTerm^{n+m}).
  Comparison with Sp_G(u) (G's operations, τ) a separate later lemma.
- 2026-11-11 G's operations committed as constructions (45, 942e8ee2, shared
  586/0), parametric in c2's (al, eqal, commH). (d): CEvT, CSolT in check.
  Split: c2 after h-sets: cmpI / (K) / (U) / (E), then (d)(1)-(3) (evaluation
  of classes, uniqueness, mere surjectivity); 45: Lemma 59 (local
  representation as parameter), Cor 15 / Lemma 16 at yo F1, Sol vs Sp_G, (d)'s
  plumbing.
- 2026-11-11 Lemma 59 at the total site needs Lemmas 66, 67, Prop 69 (P2.1-
  P2.4), none at the total site yet. RULING (4e): only NON-DEPENDENT targets
  are needed (G^{Sp u}, N_D^{Sp u}: closed D-modal Q); route: maps Δ -> Q ≃
  maps D Δ -> Q (Lemma 66, non-dependent), then Prop 13. Order (45): Cor 15,
  Lemma 16 at yo F1 and Delta N, non-dependent 66 / 67, Lemma 59. "D-modal" =
  EquivOp of tau_P at the total site. Π at the total site = fibPi-T.
- 2026-11-11 D PRESERVES H-SETS (c2, 3e42372f; CTotSet1-12, CwFHed5-6):
  setD : isProp Id_{D A}(x, y) from isProp Id_A over G.A.A (Hedberg). Verified
  by 4e: 14/0. Next (c2): preI / cmpI / (K) / (U) / (E), then (d)(1)-(3).
- 2026-11-11 (45) Cor 15 at the total site (CTotC15.cor15: EquivOp of D tau_A),
  in shared check; CEvT, CSolT committed 60eb0578. Lemma 16 at the total site
  sized 1,000-1,300 lines (zig homotopy 700-1,000 + transfer 150-250 +
  instances). 4e asked 45 to check a multiplication route (mu . D tau ~ id,
  mu . tau_D ~ id + Cor 15) first.
- 2026-11-11 Lemma 16: multiplication route checked and REJECTED (45): a
  natural mu is the zig's bridge M itself, its two laws need homotopies of the
  same kind as the zig's p, q, and it needs more transfer than the zig. Plan:
  transfer of EquivOp along homotopies (generated G-version), then the zig at
  the total site reusing CTotL14e-g. 1,000-1,300 lines.
- 2026-11-11 (45) Cor 15 committed (630f12f6). HtpyEq / GHtpyEq: EquivOp moves
  along homotopies (in check). CTotL16a: Lemma 16 at the total site from the
  zig homotopy as a parameter (private). Only open piece of Lemma 16: the zig.
  c2: (U)/(E)/(K) internally (code-level copairing ruled out).
- 2026-11-11 (c2) CPreI committed (c2cb1990: preI generic in the closed map,
  cmpI). (K) internal: (U) 4-5 files, (E) 3, (K) 1; (U) stated for any
  presentation s, so (d)(2) reuses it.
- 2026-11-11 RULING (4e): the zig and Lemma 16 for the CONCRETE C only
  (constant objects: object equations refl), header says so; generic Lemma 16
  (~1,300-1,700 lines) recorded as optional. Arith[vl] vs Arith[a] arities:
  cheapest fix (instantiate Chains at Arith[a] if consumers allow, else
  transport). CTotL16b (weights) checks privately.
- 2026-11-11 (c2) (K): reading lemma CCmpU1-7 checks privately; remaining (U)
  4-6 files, (E) 3, (K) 1-2 (HomT a set, generic in s, t): 9-11 files.
- 2026-11-11 LEMMA 16 AT THE TOTAL SITE (45, concrete C, private, shared check
  running): CTotL16a-l, lemma16 : EquivOp of tau_{(D A)[tau_G]}, no parameter
  left (zig built). C-generic parts (16a, c-e) separated from concrete ones
  (16f-l). Next (45): instances at yo F1 and Delta N, non-dependent Lemma 66 /
  67, Lemma 59 for G^{Sp u} and N_D^{Sp u} (sizes first).
- 2026-11-11 Lemma 16 committed (45, dbd38e08, shared 622/0). Verified by 4e:
  CTotL16a-l, CTotC15, CPreI 14/0.
- 2026-11-12 G AND N_D ARE D-MODAL (45, fb624f08, shared 626/0): CCopy4-6
  (per-copy assembly of fibration structures, generic; U(yo F1) levelwise
  fibrant), CTotL16m (YoMod, NMod). Lemma 59 (non-dependent, levelwise at each
  (y; u, f)): ~550 lines; Lemma 66 uniqueness componentwise from Lemma 14 +
  Q a set (no zig at Sp u), existence via tau_Q^{-1} . D f.
- 2026-11-12 Lemma 59 (45): parametric (context, levelwise fibrant A, closed
  modal set Q, local representation as data); internal equivalence read at the
  point (internal Id, not metatheory equality). AXIOM STATEMENTS assigned to c2
  after (K): G[X_n] := Σ (s : ΔShape_n) G^{k(s)} (shapes + coefficient
  vectors, no inductive types in the model), ev by recursion on shapes, Pr,
  Sp(u), G^{Sp u}, N_D^{Sp u}, the five propositions of S1-S2 + projectivity.
- 2026-11-12 Axiom statements (c2): 5-7 files; Pr := Σ (n m : ΔN) (G[X_n])^m
  internal (literal to SAG). After (K).
- 2026-11-12 RULING (4e) Lemma 59: per y and per SYNTACTIC u (metatheory
  parameters), an internal equivalence of closed types of the copy y:
  U(Π_{Sp u} Q)|_y ≃ U(Q)|_{y.u}; one rho, one D rho^{-1}; no strictly stable
  representation interface (uniform version ~1,000-1,300 not needed). The
  axioms eliminate "merely γ = image of a syntactic u" inside their Tr0 goals;
  u constant, objects constant, so cube-uniformity is automatic. ~600-700.
- 2026-11-12 Lemma 59 at fixed (y, u) (45): ev committed (17252136, CL59a);
  inverse built (CL59b-e, private / shared check: generic D s^{-1} for a
  context map with U s a levelwise equivalence). Remaining: two homotopies +
  QinvEq, ~300-400 lines.
- 2026-11-12 (45, 07173425, shared 631/0) Lemma 59: both maps (ev, inv) exist.
  RULING (4e): state Lemma 59 as quasi-inverse data (ev, inv, H1, H2) with
  internal Id-homotopies at G0 over the copy's context; no EquivOp packaging,
  no restriction of fibration structures to the poset kit. ~400-500 remaining.
- 2026-11-12 Lemma 59: H1, H2 as internal Id at G0 over Sy (points at copy y),
  ev / inv lifted by transport along z = y (+~100 lines), since the axioms'
  levelwise proofs live at G0 over U Γ.
- 2026-11-12 Lemma 59: the Id form at G0 forces (1) (G0 line kit restricted to
  a copy vs the poset kit, ~200). Ruling: (a) now (path homotopies at the copy,
  ~450); (1) + G0 Id form deferred to the design of the axiom proofs.
- 2026-11-12 Lemma 59: path homotopies need Kan composition at the copy, so
  (1) is needed in every form. Ruling: (1) generic now, (2), (3), then the
  G0 Id lift (~100): ~750-850 lines total for Lemma 59.
- 2026-11-12 (45, dae33c46, shared 633/0) restriction of fibration structures
  G0 -> copy (CCopy7, CCopy8, FibR). Lemma 59 H2: 4e's componentwise
  argument is NOT natural along C-maps (levelwise centres); H2 by
  D-functoriality instead (ev'' and D rho . (D rho)^-1 ~ id, tau_Q^-1 . tau_Q
  ~ id, both G1-natural); generic lemma "CEqCen inverse . al ~ id". ~600 left.
- 2026-11-12 (45) EqQinv / GEqQinv (private): an EquivOp gives a quasi-inverse
  with path homotopies, any base. Lemma 59 remaining: G1 fibrancy of D yo(y.u)
  and D(yo(y).A) (~250; CCopy6.YoF generalised to any F), H1 / H2 / lift (~350).
- 2026-11-12 (45, 35082fa3, shared 642/0) Lemma 59 H1 : ev . inv ~ id at the
  copy (CL59k); EqQinv / GEqQinv, CCopy9 (yo F levelwise fibrant, any F),
  CL59g-h, CTotTauDM. H2 in progress (CL59l-m private), then the G0 Id lift.
- 2026-11-12 LEMMA 59 COMPLETE at fixed (y, u) (45, 35082fa3 + dc046362,
  shared 649/0): CL59r.L59 gives ev, inv, path homotopies h1, h2 and their
  internal forms at the copy, from ef (rho a levelwise equivalence) and mQ (Q
  D-modal). Verified by 4e: CL59l-r 7/0. G0 reading deferred to the axiom
  proofs. Next (45): (d) plumbing (ef for rho; Sol vs Sp_G), design of the N
  axiom proof, then G's laws / 0 / 1.
- 2026-11-12 Prop 58's ef for rho (45): per copy y', domain moved to
  HomT(y.u, y') by alpha; E side = Sp_G(u) (G-based, as c2 builds it), so no
  strict cart: (1) with the E side as a parameter, then the comparison Sol ≃
  Sp_G per copy as its own step (tau + Lemma 14 inverse, op-compatibility of
  tau as a lemma reused by G's laws), coordinated with c2's Pr / Sp.
- 2026-11-12 (45) Prop 58 plumbing built privately: CEqCancel (2-out-of-3 for
  EquivOp), CRho1-2 (rho's ef from cE and fwd / Kd, assembled per copy). Sp(u)
  interface agreed with c2: SpU = Σ (v : G^n) Π_j Id (ev_qj(gY, v)) 0, gY_i =
  tau . yo(iota_i). G's operations re-instantiated with EqQinv's quasi-inverse
  of D cmp (carries the path needed for tau's op-compatibility).
- 2026-11-12 (45, 26d34f61, shared 655/0) CCmpY5 (G's ops from EqQinv),
  CTauOps, CCmpY6 (tau compatible with + and * up to paths). N axiom design:
  statements are two Tr types at the total site (S2), sections via
  CTotTr.sec from levelwise Tr0 elements over U Γ, built per copy after
  eliminating "merely γ = image of a syntactic u", then (B) at the copy
  (const_y : N_D|_y -> (Π_{SpU} N_D)|_y; ev . const = restriction; Lemma 59 +
  2-out-of-3), then (C) a short per-copy assembly of elements.
- 2026-11-12 Comparison Sp_G ≃ Sol per copy (45): E1 (ev^G at tau = tau of
  ev^A, induction on terms), E2 (tau . eps ~ id at the copy), cE, its
  quasi-inverse, commH: ~500-650. RULING: G's constants c_r := tau(k_r), k_r
  the global element of yo F1 sending the generator to cls (cst r) (no F0
  detour for 0, 1, phi r).
- 2026-11-12 (45) 4a4bdf37 (CCopyH: restriction of maps / homotopies to a
  copy; CL14C: Lemma 14 for yo F1 per copy), 04ebcdaa (CGBr: c2's context G
  read as a type, fibrant at G1). Comparison cE: proof parts by an INTERNAL
  implication between the equation types (natural by construction), not
  pointwise choices; ~650-800 lines.
- 2026-11-12 (c2, a7459d01, shared 683/0) (U) for cmpI: CCmpU1,5,6,9-30,
  maps out of F2 with equal composites are equal. Next (c2, reordered): axiom
  statements, then (E) (12-20 files), (K), (d)(1)-(3).
- 2026-11-12 RULING (4e): axiom statements per METATHEORY u = (n, m, shapes)
  (external schema), as Tr types over contexts of G-powers: the total site has
  no fibrant constant types (ΔE only at the poset base). Internal ∀ over the
  model's naturals = later step (needs ΔE fibrant at the total site + "N_D's
  elements are merely numerals" via KL). N_D fibrant at G1 by Lemma 12F on
  ΔN's G0 fibration (45).
- 2026-11-12 Correction (c2): duality cannot be a schema over shapes (the
  polynomial's degree is inside the truncation); needs (A) ΔE fibrant at G1 +
  pack, G[X_n] := Σ (d : ΔN) G^{k(n,d)}. N statements and projectivity can be
  per u. Plan: common part + N statements, then (A) (try generating CConst as
  an FB member first), then duality statements, then (E).
- 2026-11-12 CORRECTION (c2, 45): 4e's c_r := tau(k_r) is NOT strictly natural
  (k_r natural only up to its constant datum, a path). RULING: constants as
  the binary operations (Höfer Constr. 44/45, arity 0): yo F0 -> 1 levelwise
  equivalence (nullary (U)/(E)), D of it an equivalence (Prop 13), EqQinv
  point of D(yo F0), cst r := D(yo(SubC[F1, F0, cst r])) of it; E1's cst case
  from the quasi-inverse homotopy. 45: CApOp2, CHtpyAlg (generic E1) in check;
  CNDFib (N_D fibrant at G1) checked privately.
- 2026-11-12 (45, ec2d0837) CApOp2, CHtpyAlg (generic E1). Nullary (U)/(E)
  (Hom(F0, y') contractible) goes to c2 with (E); 45 builds the constants
  with it as a parameter.
- 2026-11-12 (c2) statements built privately: CAxPow, CAxEv, CAxOps, CAxSp,
  CAxN (Nsurj, Ninj), CAxProj (Def 73 as a schema over (D, s, P)); install
  after 45's CNDFib. (A) for duality: a Cyl for the Groth site of CM.IC,
  CConst / pack as FB members, ΔN and the shape family at G1 (4-6 files),
  then the duality statements (2 files). 4e reads the statements before
  reporting them.
- 2026-11-12 (c2, private) constant types at the total site: CGrothCyl
  (cylinders for the Groth site of any IC), GCConst / GCConstLam (FB members),
  CAxDelta (ΔN fibrant at G1). Duality: SURJ now (G[X_n] := Σ (d : ΔN) Π (α :
  ΔMon_n). (|α| ≤ d) -> G); KERNEL after (E)/(K) (needs G[X]'s ring structure
  on coefficient vectors, 6-10 files).
- 2026-11-12 (45) CNDFib committed (3fc8d296: N_D fibrant at G1). Constants
  (private): CContrEq (contractible type -> closed type equivalence), CCst2
  (yo F0 -> 1 levelwise equivalence per copy, Prop 13), parametric in c2's
  cF0 (isContr HomT(F0, y)). Next: point of D(yo F0), cst r, compatibility.
- 2026-11-12 STATEMENTS committed (c2): 39547ee6 (CAxPow, CAxEv, CAxOps,
  CAxSp, CAxN, CAxProj), cb4e889f (CFibSeg + GCConst, GCConstLam), 8cdce29b
  (CGrothCyl, CAxDelta, CAxMon, CAxElOps, CAxSurj). READ by 4e against SAG /
  jonas: Sp(u), B^{Sp u}, Nsurj / Ninj, duality surjectivity correct.
  CORRECTION requested: CAxProj must quantify over D-MODAL P only (Def 73 is
  in the inner model; Lemma 59 needs Q modal). Kernel statement after (E).
  Constants cV, cN and (al, eqal, commH) still parameters.
- 2026-11-12 (c2) projectivity fixed (6864ce41: P D-modal, mP). Generic (U)
  for any presentation (CUG13-30) and CUF0 (Hom(F0, y) contractible, cF0) in
  shared check; next (E) for cmpI, then (K).
- 2026-11-12 G'S CONSTANTS committed (45, 8ee2188a: CContrEq, CCst2, CCst3),
  unconditional with c2's cF0 (4b629d42). HomT(F1, y') ≃ Q_y' assigned to c2
  (F1 instance of its (K) route); 45 takes it as a parameter.
- 2026-11-12 (45, 119aa918) CCst4: at a copy, cst r ~ tau(kc). E1's instance
  next (~250): A side Q_y' with strict operations, tau' := tau . beta .
  psi^{-1}, additivity of codes as paths (Kan composition).
- 2026-11-12 (45, 33c99ae6, shared 732/0) E1 AT A COPY (CE1Copy): evaluation
  in G at tau'-images = tau' of evaluation in Q_y', all terms; CRestrHT.
  Parameters left: phi (c2's CEv6), cop / sec (c2's (K)), cTp and the code
  readings (45).
- 2026-11-12 (45) E1 at a copy fully assembled (CE1Fin; CPhi, CFibTc, CTrips,
  CRead*) except the pairing of codes (cop, sec1, sec2), to be read from c2's
  (K). Then cE and commH.
- 2026-11-12 (c2) (K) for cmpI: injectivity, propositional fibres, the fibre
  element over nil.HTT.S1.S2 (CCmpK3-18, in check). Truncation not stable
  under substitution: merely-a-class eliminated at its native base into
  Π-motives that are propositions; to be packaged as a generic lemma (recurs
  in (d)(3) and the axiom proofs).
- 2026-11-12 (45) E1 at a copy complete privately (CCop, CE1Done), commit
  after c2's CCmpK30-32. Next: al / eqal / commH from c2's (K) (G's operations
  unconditional), then cE and commH for Prop 58.
- 2026-11-12 (45, private, commit after c2's CCmpK3 / K30-32) G'S OPERATIONS
  UNCONDITIONAL: CAlEq (al = cmpI, eqal from c2's cop, commH by beta . alpha
  = id), CGRing (G's +, x, constants with tau-compatibility and E1 at every
  copy, no assumed inputs). G's RING LAWS themselves still to do (after Prop
  58). Next (45): cE and commH for Prop 58.
- 2026-11-12 (c2, 65956474) (K) FOR cmpI COMMITTED: the comparison's internal
  equivalence; generic CMsElim (eliminate a truncation at its native base into
  a proposition, then substitute) and CSEl; F1 instance CEv7/8 (1ac63fe4).
  Next (c2): duality kernel statement, then (d)(1)-(3).
- 2026-11-12 (45, 8db1a3c3, shared 783/0) G'S OPERATIONS COMMITTED with no
  assumed inputs: CCop, CE1Done, CAlEq, CGRing.GR. Next (45): cE for Prop 58
  (identity on the base code + internal implications Sp ⇔ Sol by E1 and tau'
  an equivalence on fibres at the copy).
- 2026-11-12 RULING (4e) for Prop 58's data: 45 builds A = Sp(u) along gY
  (c2's CAxSp), rho, rho1; rho's Id part needs E1 at the TOTAL site (generic
  CHtpyAlg at G1 with CCmpY6 and total constants' compatibility) plus the path
  cls q_j = cls 0 through tau; Id fibres are propositions (setD, UP3, FibR,
  setQ), so cE's fibre part is a logical equivalence.
- 2026-11-12 (45, 11b5c235) total-site E1 up to constants: CLineC (line of
  codes from UG30's closed Id), CApOp2G, CHtpyAlgG; in check: CLinePre,
  CCodeH, CCompC, CE1Tot-3. Remaining for rho: total constants, the zero-code
  step, G1 homotopy -> internal Id, then A = Sp(u), rho, rho1; then cE.
- 2026-11-12 CHECKER FIX (4e, user-approved, d67086f1): the server's main-file
  key leaves out import lines, so adding files to All.seg no longer rechecks
  everything (test: 1 module, 0.63 s instead of 282). Servers restarted on the
  new binary (sag/cobar; core / sag-model stopped, restart on next use); one
  last full recheck on the first `changed` (old baseline key format).
- 2026-11-12 (45) ef737461 (total-site E1 complete, CE1Zero, CHtIdG),
  fcd283aa (CSpA, CSpA2: A = Sp(u) along gY; CEvCong; CRhoOld; CRhoId).
  Verified by 4e: 5/0. Remaining for rho: derivations q_j = 0, ev match,
  retyping into c2's EqT, Σ assembly, rho1; then cE.
- 2026-11-12 (c2, ccf4d0c7) DUALITY KERNEL STATEMENT (CAxKer, CAxPoly, CAxPack):
  over Pr.(c).(d).(h : ev_u(d, c) = 0): || Σ a e. trunc_d c = Σ_i trunc_e(a_i) *
  q_i || on coefficient vectors (convolution product, G's operations). READ by
  4e: correct form of "ker ev_u ⊆ (q)". All five statements now stated.
  Next (c2): Prop 58's (d)(1)-(3).
- 2026-11-12 (45, 806e425f + CRhoSig) PROP 58's DATA CONSTRUCTED: A = Sp(u)
  along gY, rho, rho1 (CRhoPt, CRhoTel-3, CRhoSig); CRho1's Data instantiated.
  Remaining for Prop 58: cE (comparison, per copy) + c2's fwd / Kd.
- 2026-11-12 (45, 2660255b) commH as a path homotopy (HtpyEq + CEqCancel);
  c2: readings of fwd (26b36cf3). Next (45): cE / ecE / commH per copy
  (500-700 lines), closing Prop 58's ef modulo c2's (d)(1)-(3).
- 2026-11-12 (c2) (d)(1) fwd, (d)(2) injective, T0 a set, propositional fibres
  committed (8932383a, 9e8db646, 000beafc). (d)(3) mere surjectivity: (K)'s
  route FAILS (the substitution hom out of A_{x.u} needs a CLOSED proof that
  it kills the relations; ours is open). Ruling: function-ring route (target
  Fun T0 Q_y, everything closed in t : T0), needs Q_y's ring laws at open
  elements (reusable module), 15-20 files.
- 2026-11-12 USER DECISION: the FULL FIX of the truncation (SAG.pdf §8.3
  location-free, strictly stable, code former tr : U -> U, bridge to the 37
  existing files), ~1,100-1,500 lines, then open-context quotient elimination
  and (d)(3) by the (K) route (~25-30 files in all). Alternative weighed: the
  comparison map st only (~10-12 files, no codes). c2 plans first.
- 2026-11-12 Full-fix plan (c2, approved): CTrLF1-3 (location-free trees,
  good, code), CTrLFBij1-3 (natural bijection with core's good trees; core's
  files untouched), CTrLFTy1-4 (Tr' with its interface, fibrancy rebuilt from
  F), CTrLFSt1-2 (stability as an equality of types; tr : U -> U), CTruncAtS;
  ~1,300-1,400 lines, poset base first. Risk: the bijection's naturality.
- 2026-11-12 (c2) stable truncation, simplification: location-free normal
  forms = core's normal forms over the representable y(X) with A[x^]; the
  presheaf laws of the action need st as an algebra map + core's uniqueness +
  pushforward functoriality. Revised total 1,600-1,900 lines (cap 2,200 before
  re-asking). Open (4e): propositional extensionality's base instance (CwFS4)
  is still a parameter, the one real assumption left.
