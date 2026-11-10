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
