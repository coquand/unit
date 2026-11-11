# Simplified plan for the SAG axioms in PSh(∫C)_D (route R2)

canonicity-4e, 2026-11-11, for criticism by canonicity-45 and canonicity-c2
before any further code. Worked backwards from the three axioms.

## S0. Every axiom is a proposition

Duality ("ev is an equivalence"), constancy of N and projectivity are
propositions of the model. So we never need Prop 17 as a statement about
maps. We need one lemma:

**Key Lemma (KL).** Let Γ be a fibrant context over ∫C, and P a D-modal
family of propositions over Γ. If P is levelwise inhabited (a function, in
the base's type theory, giving an element of P(x, γ) at every point γ of Γ
at x), then P has a global section over Γ.

Proof: P is levelwise contractible (inhabited proposition), so U P is
levelwise trivially fibrant. Lemma 12 (trivial half) makes D P uniformly
trivially fibrant, so D P has a section, and the inverse of τ_P (P modal)
moves it to P. This is c2's II.4 argument, in general.

Each axiom is then: (i) write it as "P has a section over Γ" with P a
truncation (hence modal by Lemma 31) or an identity type of a set;
(ii) prove the levelwise inhabitation, which is algebra at one stage.

## S1. Duality without the presented algebra ⟨u⟩

Duality for u = (n, q_1..q_m) is equivalent to two statements about the
evaluation map from coefficient lists ev_u : G[X_1..X_n] → G^{Sp(u)},
with Sp(u) = {x : G^n | q(x) = 0} (a Σ / Id, no quotient):
- surjectivity: over the context Pr.(f : G^{Sp u}),
  P = ||Σ (p : G[X]). ev_u p = f||;
- kernel: over the context Pr.(p : G[X]).(h : ev_u p = 0),
  P = ||Σ (c : G[X]^m). p = Σ c_i q_i||.
The hypotheses go into the context, so no Π-type has to be shown modal.
The equivalence with "G[X]/(q) → G^{Sp u} is an equivalence" is a generic
lemma of univalent algebra (a ring map is an equivalence from the quotient
iff it is surjective with kernel (q)). It can be checked in Unit once, in
Tier 1 style.

**Removed:** ⟨u⟩_{T/G} at the total site, Lemma 52, the word problem over G,
and so the second universe step (LEDGER 5b).

Levelwise at a point (y; u, f), by Lemma 59 (fibre of Π over the locally
represented Sp(u)) the fibre of G^{Sp u} is A_{y.u} = A_y[X]/(u):
- surjectivity is surjectivity of the base quotient map;
- the kernel statement is effectiveness of the base quotient.

## S2. Constancy of N

N_D := D(ΔN). Over Pr.(f : N_D^{Sp u}): P = ||Σ (n : N_D). const n = f||.
Over Pr.(n m : N_D).(h : const n = const m): P = ||n = m||. Levelwise: Lemma
14 (τ_ΔN is a levelwise equivalence) and Lemma 59. This is the cheapest
axiom, and the first target.

## S3. Projectivity at a fixed context

Definition 73 as the axiom for one generic family. No strict stability of
the truncation (c2's (b) dropped). c2's pushforward of extension algebras
gives the lax comparison and fibrancy.

## What remains to be built

1. Base: c2's truncation with fibrancy (pushforward route), Prop_U, the
   Voevodsky quotient Q(ΔE, ~) with ~ small, eliminator into h-sets,
   surjectivity and effectiveness, all at (a, a+).
2. Base algebra, only:
   - objects of C as iterated (relative) presentations, so that x.u is
     strict concatenation (no choice of representatives);
   - A_x = Q(ΔE_x, ~_x) with E_x the metatheory terms over k in all
     generators; ~_x small, because ∃ over a quotient reduces to ∃ over
     representatives;
   - C's morphisms (Construction 39) and strict composition;
   - the universal property of x.u (Prop 58's base part).

   Not needed: general free models, Lemma 50's pushouts, tensor products,
   general Lemma 42.
3. Sites: GrothCB, SliceCB.
4. Cobar over ∫C: D (Def 10), Lemma 12 (both halves), Lemma 14, Lemma 16,
   Lemma 31 (modality of R B), Lemma 54 / 59. Prop 13, Prop 17 and
   Theorem 29 are NOT needed.
5. G = D(yo F1) with its ring operations (Construction 44, via yo on C's
   morphisms); Pr, Sp(u), G^{Sp u}, N_D; KL; the three axioms in the forms
   S1–S3.

## Questions for the critics

(Q1) Is KL right as stated (Lemma 12's trivial half needs levelwise trivial
fibrancy at slices: does a levelwise inhabited proposition give it)?
(Q2) Iterated presentations as objects: do they make x.u strict, and keep
every A_x at level a+?
(Q3) Is anything in step 4 still needed beyond what is listed (e.g. for the
fibres of G^{Sp u} or for the ring structure of G)?
(Q4) The sizes of 1–5.

## Corrections after criticism (canonicity-c2, accepted)

- KL's hypothesis "levelwise inhabited" means: an ELEMENT of U P over U Γ at
  each x of C, natural in the cube direction (internal to the base), not a
  bare choice of points. No naturality in C. P levelwise fibrant; no
  hypothesis on Γ.
- Lemma 12 gives a section of D P over D Γ; pull back along τ_Γ and use a
  C-natural map (D P)[τ_Γ] → P. For P = R B that map is explicit
  (r: read at the chain of length 0, weight 1, at the identity). So
  Lemma 31 / D-modality of P is not used.
- The axioms' propositions are all truncations, with Tr A := R (Tr0 (U A)).
  A levelwise element of Tr0 gives a global section of R B by the
  adjunction El(U Γ, B) = El(Γ, R B) alone. KL is then the JUSTIFICATION
  that R Tr0 U is the truncation of the inner model (elimination into
  modal propositions); it is proved, but it is not on the axioms'
  critical path.
- Levelwise surjectivity of the base quotient is an element of Tr0 over
  the base context, natural in cubes (the Voevodsky image gives exactly
  this), never a metatheoretic choice.
- Step 4 corrected: Lemma 16 not needed; Lemma 12 (both halves) and Lemma
  14 needed; also needed: R at ∫C with the adjunction, fibrancy and r; D on
  finite products strictly and on maps (G's operations, G^n); D preserves
  h-sets (Lemma 12 trivial half on path objects); Π at ∫C for Lemmas
  54 / 59.

## Corrections after criticism (canonicity-45), and rulings (canonicity-4e)

Accepted from canonicity-45:
- Prop 13 IS needed: G = D(yo F1) must be D-modal (Lemma 16 at yo F1, which
  uses Cor 15 = Prop 13 at τ); Lemma 59 needs D of the levelwise
  equivalence yo(x.u) → yo(x).Sp(u), i.e. Prop 13 for context maps.
- Lemma 59 is re-proved concretely at ∫C (duality-presheaf's Lemma 72 runs on
  the uninstantiable DS record). Prop 58 at ∫C (local representation of
  Sp(u) by x.u) is needed.
- G's ring structure by the direct route (operations on D-families
  pointwise, laws as paths by Lemma 11's path half).
- Constant types ΔE as fibrant types at any CB-site with cylinders.
- Maps between quotients must never rely on strict functoriality of Q.
- Iterated presentations: x.u strict concatenation; A_x = Q(ΔE_x, Δ~_x);
  the term algebra (Expr, congruence, soundness) stays in Unit.
- Ruling: the quotient-free form of duality is equivalent to the official
  one by a lemma of univalent algebra checked in Unit; its transport into
  the model is by reading, with the same status as reading (A).

Ruling on the truncation (the two critics differ): Tr A := R (Tr0 (U A))
(c2's route), because levelwise inhabitation then gives sections by the
adjunction, with no truncation at the total site. Its D-modality is
canonicity-45's argument for a proposition with a strictly natural
retraction of τ (here c2's r : D (R B) → R B); Lemma 31 in general is not
needed. KL proves that Tr is the inner model's truncation (the
right-to-left half of Prop 34).

Revised sizes (canonicity-45, c2): 14,300-20,500 lines.

Split:
- canonicity-c2: base truncation, Prop_U, Voevodsky Q, GrothCB / SliceCB,
  R at ∫C, Tr with modality and KL, then S3 (projectivity).
- canonicity-45: pilot (constant types, ring laws in an h-set ring), base
  algebra (A_x, C's morphisms, x.u), cobar layer at ∫C (D, Lemmas 12, 14,
  Prop 13 with context maps, Cor 15, Lemma 16 at yo F1, Lemma 59, Prop
  58), G with its ring structure, then S2 (N) and S1 (duality).
