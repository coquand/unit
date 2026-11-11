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
