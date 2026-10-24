# stoneseq: sequential colimits and cohomology for synthetic Stone duality

Worker B of the SSD formalisation (`SSD.pdf`, Cherubini–Coquand–Geerligs–
Moeneclaey, *A Foundation for Synthetic Stone Duality*). Design:
`../stone/DESIGN.md`; interface with worker A: `../STONE-INTERFACE.md`;
gaps of the paper: `HANDOFF-B.md` (section Gaps). Check with
`./segc sag/stoneseq changed` from the root.

## Proved (SSD numbering)

| SSD | statement | file, declaration |
|---|---|---|
| Axiom 4 | dependent choice, as a type | `DependentChoice.DC` |
| — | countable choice; DC with a total relation | `CountableChoice.cc`, `Relational` |
| Def. 2.1 | overtly discrete types | `ODisc.isODisc`, `Pres` |
| Rem. 2.2 | sequential colimits (set level), overtly discrete types are sets | `SeqColim.Colim`, `Lemma27.odisc-set` |
| Lemma 2.3 | a map of overtly discrete types is a colimit of maps of finite sets | `Lemma23.lemma23`, `lemma23-rel` |
| Lemma 2.4 | image factorisations commute with sequential colimits | `Lemma24.Images` |
| Cor. 2.5 | injective / surjective case | `Cor25.cor25-inj`, `cor25-surj` |
| Lemma 2.6 | ODisc stable under sequential colimits | `Lemma26.Lemma26.theorem` |
| Lemma 2.7 | ODisc stable under Σ, identity types, truncation | `Lemma27.sigma-odisc`, `id-odisc`, `trunc-odisc` |
| [18] | Σ, Id, ∥·∥ commute with sequential colimits (sets) | `SeqSigma`, `SeqProp` |
| — | the integers as an abelian group with decidable equality; Z ≃ N | `Integers.intAb`, `int-dec`, `toNat`, `ofNat` |
| Rem. 5.2 | H¹(X, A) = 0 (BA = A-torsors) | `CechComplex.CohZero` |
| Def. 5.3, 5.4 | Čech complex, cocycles, coboundaries, Ȟ¹ = 0 | `CechComplex.Cech` |
| Lemma 5.5 | a section gives Ȟ¹ = 0 | `CechComplex.lemma55` |
| Lemma 5.6 | Ȟ¹(S, T, A^T) = 0 | `CechComplex.lemma56` |
| Lemma 5.7 | Ȟ¹ = 0 and local trivialisations give a trivial family | `CechComplex.Lemma57` |
| (5.9) | a sequential colimit of exact sequences is exact | `ExactColim` |
| §3.1 | sequential limits, families and cones over an inverse sequence | `SeqLim` |
| Lemma 5.9 (generic) | Ȟ¹(lim S, K, G) = 0 for a cone K over finite inhabited T, if Φ₁ is surjective and Φ₂ injective | `Lemma59.Lemma59.Theorem.h1` |
| Lemma 5.8 | Σ T → S is merely a limit of surjections of finite sets; its fibres are the finite families | `Lemma59Stone.Over.lemma58`, `FibreSeq.Fibres` |
| Lemma 5.9 | Ȟ¹(S, T, Z) = 0 for S, T x Stone, T x inhabited | `Lemma59Stone.Over.lemma59` |
| (5.9) | Cor. 3.7 with values in Z on fibre products: Φ₁ onto, Φ₂ injective | `Lemma59Fibres.Over.Lemma59Fibres` |
| Lemma 5.10 | H¹(S, Z) = 0 for S Stone | `Lemma510.Over.lemma510` |
| Cor. 5.11 | (BZ)^S is connected with loop group Z^S (a delooping of Z^S) | `Cor511.Over.Cor511.connected`, `loop-equiv`, `loop-hom` |
| Thm. 5.16 (vanishing) | for a Čech cover (X, S): H¹(X, Z) = 0 iff Ȟ¹(X, S, Z) = 0 | `Thm516.Over.Cover.theorem` |
| Thm. 5.16 (sets) | for a Čech cover: Ȟ¹(X, S, Z) (cocycles/coboundaries) ≅ ‖X → BZ‖₀, [b] ↦ [α_b] | `Thm516Set.Over.Cover.theorem` |

B3 uses worker A's Remark 3.4, Corollary 3.7, Theorem 4.18, Lemma 3.10,
Corollary 3.9 and local choice (Axiom 3), through links to `../stone/`.

B4: Theorem 5.16 in forms (A) and (B) of `../stone/DESIGN.md` §5 (chosen by
the user, 2026-10-24); not the group isomorphism (form C), and not Lemmas
5.13-5.15, whose route the proofs do not follow.

Supporting results not in the paper: cofinal reindexing (`SeqSub`), the
diagonal of a grid of sequences (`SeqGrid`), finite sets closed under Id, ∥·∥
and Σ (`FiniteClosure`), finite choice into `U l+` (`Finite.Up`); Ȟ¹ = 0
invariant under equivalence of (S, T), fibres of equivalent maps
(`CechTransfer`); fibres of a map of sets and the Čech groups of the fibre
family as functions on fibre products (`FibrePairs`).
