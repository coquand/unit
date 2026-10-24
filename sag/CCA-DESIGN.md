# Cohomology in synthetic Stone duality (CCA.pdf): design for workers A and B

Papers (in /Users/coquand/CANONICITY): `CCA.pdf` (Cherubini–Coquand–Geerligs–Moeneclaey,
*Cohomology in Synthetic Stone Duality*), `DW1.pdf` (Wärn, *Eilenberg–MacLane
spaces and stabilisation in HoTT*), `SSD.pdf` (the base paper, formalised in
`stone/` and `stoneseq/`).  Text: `pdftotext -layout CCA.pdf`.

Status (2026-10-24): design only; nothing built.  Starts after worker B of
the SSD project (`stoneseq/`) has stopped and `stone/`, `stoneseq/` have been
merged into `unit`.  All paths below are relative to `unit/sag/`.

## 1. What is built already (do not redo)

- `stone/` (SSD worker A; README: `stone/DESIGN.md` §6): Booleω, Sp, Axioms
  1–4 (`StoneAxioms`), open/closed propositions (`OpenClosed`), Stone spaces
  (`Profinite.isStone`), Lemmas 3.1/3.2, Cor. 3.7 (`Cor37`: N^(lim E) =
  colim N^(E n), and the compactness lemma `Cor37...Vanish`), Thm 3.11,
  Cor. 3.12–3.14 (`Thm311`), finite subcovers (`Compact`), Remark 3.4 for
  surjections (`Remark34.SurjLim`), compact Hausdorff spaces (`CHaus`: Cover,
  Lemmas 4.2, 4.5, 4.9, Cor. 4.3, 4.4), X x Y Stone (`StoneProduct`),
  Lemma 4.11 (`Sigma411`), 2^X in Booleω (`Lemma412`), Thm 4.18 (`Thm418`).
- `stoneseq/` (SSD worker B; README: `stoneseq/README.md`): sequential
  colimits and limits of sets (`SeqColim`, `SeqLim`), overtly discrete types
  (`ODisc`, Lemmas 2.3–2.7), countable and dependent choice, Z
  (`Integers`), torsors and H¹ = 0 (`CechComplex`), exactness of sequential
  colimits (`ExactColim`), SSD Lemmas 5.7–5.10, Cor. 5.11.
- `pn/Torsor.seg`, `pn/TorsorId.seg`, `pn/Gerbe.seg`: G-torsors, BG, gerbes.

## 2. Scope (CCA numbering)

In scope:
- §2.1–2.2 (only what is not in `stone/`, `stoneseq/`: Lemma 2.1.6,
  Lemma 2.1.7 from Remark 3.4, Prop. 2.1.4 (iii) and (v) as stated).
- §2.3 Scott continuity for Stone spaces: Lemmas 2.3.3, 2.3.4, 2.3.6,
  Props 2.3.5, 2.3.7, 2.3.9, Thm 2.3.11.
- §2.4 Barton–Commelin axioms: Lemma 2.4.2, Props 2.4.3–2.4.5, Thm 2.4.6.
- DW1 §2–§3 and §4.1: torsor deloopings T X, Lemma 4, Cor. 5–8, deloopings of
  maps (Lemma 9, Cor. 11, 12), K(A, n) for A abelian and all n.
- Appendix A, §3.1 (non-abelian H¹), Appendix B, §3.2 (Hⁿ(S, A) = 0 for S
  Stone), §3.3 (Thm 3.3.2, see §5 below).
- §3.4 with the interval defined without reals (§4 below), Appendix C.

Out of scope: Prop. 3.4.5 (needs n-truncations of arbitrary types),
DW1 §4.2–4.4 (spheres, cup products, Steenrod squares).

## 3. Two workers

| | owns | first track | after the join |
|---|---|---|---|
| **A** | `cca/` | §2.1–2.3 Scott continuity; the interval (§4) with Lemma 3.4.1, Thm 3.4.3 (i), Lemma C.0.5 | §2.4; Thm 3.4.3 (ii), (iii); Lemma 3.4.4 |
| **B** | `em/` (plain HoTT, no SSD axioms) and `ccacoh/` | `em/`: DW1 §2–§3, §4.1 (K(A, n)); Appendix A; Appendix B | `ccacoh/`: §3.1, §3.2, §3.3 |

Join points:
- B needs A's Props 2.3.5, 2.3.7, 2.3.9 (for Lemma 3.1.5, Thm 3.2.5, Thm
  3.3.2) and Lemma 2.1.7.  A announces them first, early.
- A needs B's Prop. 3.1.8 and Thm 3.3.2 (or its vanishing form) for Thm
  3.4.3 (ii), (iii), and K(A, n) for Lemma 3.4.4 (iii).
Each side announces finished, stable files in `CCA-INTERFACE.md`; the other
side symlinks them (never edits them).

## 4. Representation choices

- **Overtly discrete coefficients.** A family of overtly discrete groups is
  `G : X -> Group` with `(x : X) -> isODisc (G x).carrier`.  "Overtly discrete
  = countably presented" (CCA Remark 2.2.4) is not needed and not proved;
  state results with overtly discrete coefficients.
- **Cohomology.** H¹(X, G) = 0 as in `stoneseq/CechComplex.CohZero` (every
  section of BG is merely trivial).  Hⁿ(X, A) = 0 as "Π x. K(A x, n) is
  0-connected" (CCA Lemmas 3.2.2–3.2.4 only use this form).  The group
  Hⁿ(X, A) = ||Π x. K(A x, n)||₀ is needed only for Thm 3.3.2 as stated; set
  truncation by replacement (image in `X -> Prop`), as `Truncation` does for
  propositions.
- **K(A, n)** (B, `em/`): DW1's torsor construction.  K(A, 1) = A-torsors
  (`pn/Torsor`); K(A, 2) by DW1 Cor. 8 (A abelian); K(A, n+1) = T(K(A, n)) by
  Cor. 7, by recursion on n (a split on n producing the pointed type together
  with its connectivity, truncation and loop-space equivalence).  Only the
  existence half of DW1 Thm 2 is needed (no Whitehead principle).
  Connectedness and truncation levels by DW1's recursive definition
  (footnote 2), indexed by `Base.Nat` with an offset for -2, -1.  Universe
  size: T X is large; make it small with `Replacement.Images` as
  `pn/Torsor.seg` does (DW1 footnote 1).
- **The interval** (A, `cca/`): I = 2^N / ~ with α ~ β iff for all n,
  |csₙ(α|n) − csₙ(β|n)| <= 2^-n, where csₙ is computed on dyadic numerators
  (natural numbers over 2^n): no rationals or reals.  ~ is a closed
  equivalence relation, so I is compact Hausdorff (quotient of a Stone space
  by a closed equivalence relation, CCA Prop. 2.4.3 (iii)).  CCA Def. 3.4.2
  (I∼ₙ^k) and Appendix C then only use this description.  Record in the
  gaps that I is not identified with the Dedekind/Cauchy interval.

## 5. Open decision: the form of Thm 3.3.2 (worker B, 2026-10-24)

State of B when this was written: K(A, n), K(h, n), fibre sequences of
short exact sequences and their exactness in the 0-connected form, ε,
Lemmas 3.2.2–3.2.4, Thm 3.2.5, Cor. 3.2.6, §3.1 in the vanishing form,
all checked (`CCA-INTERFACE.md`).  Three forms of Thm 3.3.2, for X with a
Stone S ->> X (S x the fibres) and overtly discrete A:

- **(C) all degrees at once, vanishing.**  If Ȟ¹(X, S, B) = 0 for every
  family B of overtly discrete abelian groups over X, then Hⁿ(X, A) = 0
  for all n >= 1.  Induction on n with the H-side of Lemma B.0.4 only:
  S is a Čech cover (Thm 3.2.5 for the Stone S x^k, Cor. 3.2.6 for
  Σ_x S x^k), so for 0 -> A -> A^S -> L -> 0 exactness (`em/Exact`) gives
  Hⁿ⁺¹(X, A) = 0 from Hⁿ(X, L) = 0, the induction hypothesis (L is
  overtly discrete); n = 1 is Prop. 3.1.8.  Small (all ingredients exist).
  Enough for Thm 3.4.3 (iii): with Ȟ¹(I, T, B) = 0 for all B (the
  computation of (ii), Lemma C.0.5), Lemma C.0.6 is then not needed.
- **(B) degree by degree:** Hⁿ(X, A) = 0 iff Ȟⁿ(X, S, A) = 0.  The
  induction compares Hⁿ(X, E) -> Hⁿ(X, L) with its Čech counterpart, so
  it needs the comparison at lower degrees as a natural bijection: higher
  Čech complexes (Def. 3.3.1), Lemmas B.0.2, B.0.5 (long exact sequence of
  Čech complexes), B.0.6 (and the missing B.0.7), set truncations
  ||Π K||₀ and the maps between them.  Large.
- **(A) the natural group isomorphism** as stated: (B) plus the group
  structures on Hⁿ and Ȟⁿ and naturality.  Largest.

B's recommendation: (C) now (it unblocks Thm 3.4.3 (iii)); (B)/(A) only if
wanted.  Appendix B beyond the H-side of B.0.4 is then not needed.

**Decided (user, 2026-10-24): form (C).**  Afterwards (user, same day)
the degree-1 set-level bijections were added: Cor. A.0.7, A.0.8
(`em/CorA07`) and Prop. 3.1.8 as Ȟ¹(X, S, G) ≃ H¹(X, G)
(`ccacoh/Prop318Set`); no group structures.

**Revised (user, 2026-10-24, on worker A's finding): form (C').**  The
hypothesis of (C), Ȟ¹(X, S, B) = 0 for EVERY overtly discrete B, fails
for X = I (a family B of subgroups of Z with a non-trivial torsor).  New
statement: if Ȟ^(m+1)(X, S, A) = 0 for all m, then H^(n+1)(X, A) = 0 for
all n.  Proof: the induction of (C) over the class of overtly discrete B
with all Ȟ^(m+1)(X, S, B) = 0, which is closed under L B = B^S / B by the
Čech dimension shift (vanishing form): (1) Ȟ(X, S, B^S) = 0 by the cone,
(2) L-cochains lift to B^S-cochains (H¹ = 0 on the Stone
(x : X) * S(x)^(k+1)), (3) a diagram chase.  Cochains and δ: worker A's
`cca/Cochains`.  Built: `em/CechHigher`, `em/FibreTorsor`,
`ccacoh/LiftStone`, `ccacoh/Thm332C`.

**Form (A), plan of worker A (2026-10-24, user's request, items 8).**
Alongside `Thm332` / `Thm332C` (unchanged).  X with q : S ->> X, S x the
fibres, S a Čech cover (Def. B.0.3, `Thm332.Cov`); coefficients: families
B of overtly discrete abelian groups (closed under E B = B^S and
L B = B^S / B).  Pₘ(B) = (x : X) -> K(B x, m).

1. Groups.  Hⁿ(X, B) = ||Pₙ(B)||₀ (set quotient by replacement, as
   `CorA07.H1`), with the group structure of Ω P_(n+1)(B) ≃ Pₙ(B) (`Eps.psi`):
   path composition (n = 0: pointwise, `CechZero`).  Ȟⁿ(X, S, B) =
   cocycles / coboundaries (`Cochains.Cech`), pointwise addition.  Maps
   h_* from K(h, n) pointwise, resp. h o -.
2. H-side lemmas (plain HoTT, em/):
   - K is a functor: K(g h, m) = K g o K h, K id = id (unique-loop, as `EpsEv`);
   - PiLoop: for pointwise maps with loop F_x = e ; G_x ; e^-1,
     loop (Pi F) = psi ; Pi G ; psi^-1 (the square of `EpsEv`, generalised),
     so h_* is a homomorphism;
   - the boundary d : K(L, m) -> K(A, m+1) of 0 -> A -> E -> L -> 0
     (fibre of K p, `FibSeq`), with loop d_(m+1) = e ; d_m ; e^-1
     (Ω∂ = ∂Ω under `Fibres.omega-fib`), so δ = (Pi d)_* is a
     homomorphism, natural in morphisms of short exact sequences
     (fibre inclusions of FibSeq are unique: null-homotopies of
     K(A, m) -> K(C, m) form a contractible type);
   - Lemma B.0.4 as stated: Hⁿ(E) -> Hⁿ(L) -> Hⁿ⁺¹(A) -> 0 exact (LES of a
     fibration at π₁, π₀; Hⁿ⁺¹(X, E) = 0 by the Čech cover).
3. Čech side (em/, ccacoh/):
   - Lemma B.0.5 in the form needed and B.0.7 (supplied): for a short
     exact sequence of complexes (cochain-level surjectivity of L-lifts
     = `ccacoh/LiftStone`), the connecting map δ̌ : Ȟⁿ(L) -> Ȟⁿ⁺¹(A) is
     a well-defined homomorphism with Ȟⁿ(E) -> Ȟⁿ(L) -> Ȟⁿ⁺¹(A) exact;
   - Lemma B.0.6: δ̌ onto, since Ȟⁿ⁺¹(E) = 0 (B.0.2, `CechHigher`);
     natural in A.
4. Thm 3.3.2 (A).  Φ₀ = Lemma B.0.1.  Φₙ₊₁ is induced on cokernels:
   Hⁿ⁺¹(A) = coker(Hⁿ(E) -> Hⁿ(L)) ~ coker(Ȟⁿ(E) -> Ȟⁿ(L)) = Ȟⁿ⁺¹(A),
   using Φₙ for E and L and its naturality for p; Φₙ₊₁ is natural
   because δ, δ̌ and Φₙ are.  Statement: for each n a group isomorphism
   Hⁿ(X, A) ≅ Ȟⁿ(X, S, A), natural in homomorphisms of overtly discrete
   families.
Estimate: 10-15 files.  The hard part is the boundary d (Ω∂ = ∂Ω, its
naturality); the Čech side is algebra.

## 6. Rules (as for SSD)

- Checker: the `unit` checkout (`/Users/coquand/CANONICITY/unit`): `cabal build`
  at its root at the start of a session; check with
  `./segc sag/DIR changed|all` from that root.  Every file < 10 s, every shell command < 60 s.
- Write so that checking follows reading: `/Users/coquand/CANONICITY/seg/WRITING.md`.  Informal proof
  first in the file comment; one name per notion; refl lemmas for "by
  definition"; accessors instead of projection chains.  After each file run
  `--opened`; record in the HANDOFF any declaration opening more than ~500
  definitions.  The known cause in `stone/`: algebras built with `mkBA` /
  `mkCRing` decoded in conversions (checker matter, see `stone/HANDOFF-A.md`);
  for new structures, state "by definition" refl lemmas next to them.
- Recursion only through eliminators (`unit/doc/PRIMREC.md`); no type classes; no
  HITs (quotients and truncations from replacement); general statement first,
  instance second; lock a construction right after its characterising lemmas.
- Each worker edits only its own directories; shared files (`pn/`, `stone/`,
  `stoneseq/`, …) are read-only, symlinked.  A needed change to a shared
  file: ask the user first.  Do not commit.
- Keep a "Gaps" section in the worker's HANDOFF: statements used without
  proof, omitted verifications, broken references, citations replaced by
  proofs.  Already seen in CCA: Lemmas 2.3.6, 2.3.7, 2.3.9, 2.3.11, 2.4.6,
  3.1.5 omit their verifications; Lemma B.0.6 cites a Lemma B.0.7 that is not
  in the paper; Thm 3.3.2 has a broken reference ("in the sense of ??");
  Remark 2.2.4 is asserted without proof for groups.
