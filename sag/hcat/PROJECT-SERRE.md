# Project: Serre finiteness from homology as a colimit (sag/hcat)

## Goal

Formalise in Unit, inside the Sattler–Wärn axioms of `sag/hcat`, the constructive proof in
`~/CANONICITY/serre.pdf`:

> for all n, m : ℕ, πₘ(Sⁿ) is finitely presented.

The proof in `serre.pdf` uses two external tools: the **homological Serre spectral sequence**
and the **Hurewicz theorem**. Our homology is the copower X ⊗ A in a stable category D
(`DESIGN-HOMOLOGY.md`). The spectral sequence comes from dualising Shulman's construction
(`~/CANONICITY/sshott.pdf`, nLab "spectral sequences in homotopy type theory"). His proof
uses limits (Π, sections); ours uses colimits in D (copowers and colimits of diagrams).

## The proof to formalise (`serre.pdf`)

- A group is **f.p.** if there merely is an exact sequence 0 → Zⁿ → Zᵐ → A → 0. In a
  short exact sequence, if two terms are f.p., so is the third (Z is coherent).
- A space X is **good** if H_n(X; A) is f.p. for all f.p. A and all n.
- Lemma 4: spheres are good (Mayer–Vietoris).
- Lemma 5: if F → T → B is a fibre sequence with B simply connected, F connected and F good,
  then B is good iff T is good (Serre spectral sequence, a filtration argument on pages).
- Corollary 5.1: K(A, n) is good for A f.p. and n ≥ 2. Use the fibre sequences of
  0 → Zᵃ → Zᵇ → A → 0, of 0 → Z → Zᵐ → Zᵐ⁻¹ → 0, and of the path fibration, down to
  K(Z, 1) = S¹.
- Corollary 5.2: a 2-connected good space has f.p. homotopy groups. Use Hurewicz, then
  kill the bottom group with the fibre of X → ‖X‖ₖ₊₁.
- Corollary 5.3: πₘ(Sⁿ) is f.p. (n ≥ 3 directly, n = 2 by the Hopf fibration, n ≤ 1
  explicitly).

## The spectral sequence (dual of `sshott.pdf`)

Shulman's construction has two parts.

1. **Algebra.** A tower of fibre sequences gives long exact sequences, hence an exact couple
   (D, E, i, j, k). Its derived couples give the pages Eʳ. Convergence: for a tower that is
   bounded above, and in which each homotopy group vanishes far enough down, πₙ(Y) is a
   finite iterated extension of the E^∞ terms with p + q = n. This is constructive algebra
   of abelian groups.
2. **Topology.** The Atiyah–Hirzebruch sequence comes from the Postnikov tower of the
   coefficients. Serre is its parametrised form, via
   SpSect(X, λx. SpMap(F_x, Y)) = SpMap(Σ_x F_x, Y).

Dual for homology, in D:

| Shulman (cohomology) | here (homology) |
|---|---|
| SpMap(X, Y) | X ⊗ A (have) |
| SpSect(X, x ↦ Y_x) | colim_{x:X} B_x (to add) |
| SpSect(X, SpMap(F_x, Y)) = SpMap(ΣF, Y) | colim_x (F_x ⊗ A) = (Σ_x F_x) ⊗ A (to add) |
| Postnikov tower of a spectrum | t-structure on D: τ_{≥q}, layers Σ^q H π_q (to add) |
| LES of the tower | Hom(S, −) of the tower, by stability (have; homomorphisms open) |

Apply the fibrewise Postnikov tower to x ↦ F_x ⊗ A and take colim_x. For B simply
connected the local system x ↦ H_q(F_x; A) is constant (AbGp is a 1-type), so the layers
are B ⊗ Σ^q H(H_q(F; A)). This gives

  E²_{p,q} = H_p(B; H_q(F; A)) ⇒ H_{p+q}(Σ_x F_x; A).

Only the E² page and convergence are used by Lemma 5. Whether this agrees with the
classical Serre spectral sequence is not needed.

## State (2026-11-01)

Done in `sag/hcat` (see `DESIGN-HOMOLOGY.md`, `README.txt`, note
`unit/doc/hcat-homology.pdf`):
- copowers: functoriality, homotopy invariance, dimension, additivity, Fubini;
- excision (assuming `hpent`, the pentagon of D);
- segment `Stable`: zero object, suspensions, stability (Hom(S, −) sends pushouts to
  pullbacks);
- loop equivalence Hom(ΣS, T) ≃ Ω Hom(S, T), natural in T;
- homology groups (abelian);
- Mayer–Vietoris: middle exactness, the connecting map, exactness at H(C);
- suspension isomorphism;
- H̃_*(Sⁿ), segment `WithSpheres`.

Results are bijections of sets; homomorphisms are open.

Open in parallel (another session): deriving `hpent` from `Coh3.k5`.

## Milestones

**S1. Homomorphisms and the full long exact sequence.**
- Postcomposition is a homomorphism of the groups.
- The suspension isomorphism is a group isomorphism.
- Mayer–Vietoris is exact at H_{n+1}(X).
- The long exact sequence of a fibre sequence in D (from stability) is a sequence of
  abelian groups.

Reuse `sag/em` (`QGrp.Map`, `GHom`, `Exact`, `LES`) where it links without name clashes.

**S2. Colimits of diagrams.**
- New parameters (a sub-segment): colim_{x:X} B for B : X → Ob D, X : U k, with the
  universal property Hom(colim B, T) ≃ Π_x Hom(B_x, T).
- Copowers are the constant case.
- Prove:
  - Σ-Fubini: colim_x (F_x ⊗ A) ≅ (Σ_x F_x) ⊗ A;
  - colimits preserve pushouts, hence (with stability) fibre sequences;
  - functoriality in the diagram.

**S3. t-structure and Eilenberg–MacLane objects.**
- Parameters: truncations τ_{≥q}, τ_{≤q} with fibre sequences, connectivity of
  X ⊗ A for connective A, and H : AbGp → Ob D with π_j(HA) = A for j = 0 and 0 otherwise.
- Ordinary homology: H_n(X; A) := π₀ Hom(Sⁿ_D, X ⊗ HA).
- Prove: short exact sequences of groups give fibre sequences of the HA; H_n(pt; A) = A
  for n = 0 and 0 otherwise (the ordinary dimension axiom).

**S4. Exact couples and convergence** (pure algebra, independent of D; can start
in parallel with S1–S3).
- Graded abelian groups, exact couples, derived couples, pages Eʳ.
- Convergence for towers bounded above with eventually vanishing groups.
- f.p. groups over Z constructively: two-out-of-three, subquotients, quotients of f.p.
  by f.g.
- Reuse the coherent-ring material in sag where possible.

**S5. The homological Serre spectral sequence** (S2 + S3 + S4).
- The Atiyah–Hirzebruch sequence for colim_x of a family.
- Serre for a type family over a simply connected base: the local system is constant via
  ‖B‖₁ = 1.

**S6. Hurewicz.**
- For X (k−1)-connected: π_k(X) ≅ H_k(X; Z), comparing type-theoretic homotopy
  groups with our homology.
- Needs a map X → Ω^∞(X ⊗ HZ) (unit of the copower) and a connectivity argument.
- Compare Christensen–Scoccola (HoTT, with another definition of homology).
- This is the step most likely to need a further axiom on D, relating Ω^∞ and connectivity.

**S7. `serre.pdf`.** Lemma 2, Lemma 4 (from Mayer–Vietoris), Lemma 5, Corollaries 5.1–5.3.
- Uses K(A, n) and fibre sequences from `sag/em` (`EM`, `FibSeq`).
- Uses the Hopf fibration for n = 2 (`pi3-s2-postnikov`, or a new construction).

## Design rules

- Plain dependent type theory; no judgemental shortcut for Cat (user ruling).
- Every new axiom is a named segment parameter, in the innermost segment that needs it,
  so that each theorem's assumptions are read from where it is checked. Reports say
  "no new axioms beyond …" and list the parameters.
- Coherence: record for each milestone the internal and external level used. Expected:
  internal level ≤ 3, so external level ≤ 4. If a step needs more, stop and ask.
- Follow `seg/WRITING.md`:
  - informal proof first, in the file comment;
  - one name per notion, no local aliases;
  - lock after the characterising lemmas;
  - check `--opened`;
  - state path algebra as generic lemmas on variables, applied once (this cut `Loops`
    from 1.06 s to 0.26 s).
- Every file under 1 s; every shell command under 60 s. Check with `./segc sag/hcat changed`
  from `unit/`; stop the server at the end.
- Another session works in `sag/hcat` (witnesses, `hpent`): edit `All.seg` only by
  targeted insertions.
- No commits unless asked. Notes are concise, stamped with file name and date.

## References

- `~/CANONICITY/serre.pdf`: constructive Serre finiteness (f.p.), from the Serre spectral
  sequence and Hurewicz.
- `~/CANONICITY/sshott.pdf`: Shulman, spectral sequences in HoTT (nLab, 2024): exact
  couples, convergence, Atiyah–Hirzebruch and Serre via parametrised spectra.
- F. van Doorn, *On the formalization of higher inductive types and synthetic homotopy
  theory*, §5 (arXiv:1808.10690); Lean library *Spectral* (cmu-phil/Spectral).
- J. D. Christensen, L. Scoccola, the Hurewicz theorem in HoTT.
- `DESIGN-HOMOLOGY.md`, `README.txt`, `unit/doc/hcat-homology.pdf` (this development).
