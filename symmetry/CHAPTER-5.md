# Chapter 5 in Unit

Declarations are written `File:Module.name`. Modules of the form `Over[G]` take the group as their parameter. "Open" means that no Unit proof exists yet.

## 5.2 Group actions

| Item | Unit | Status |
| --- | --- | --- |
| Def 5.2.1 G-sets | `ChapterFive:Actions.GSet` | done |
| Ex 5.2.2, 5.2.4, 5.2.5 trivial, principal, adjoint | `GSets:Over.trivial`, `principal`, `adjoint`, `adjoint-acts` | done |
| Ex 5.2.6 the G-set Hom(H,G) | `GSets:Over.homs` | done |
| Ex 5.2.7 Ad_G = Hom(ℤ,G) | `ActionExercises:AdjointHoms.path` | done |
| Def 5.2.8 maps of G-sets | `GSets:Over.Hom`, `Hom-set` | done |
| Ex 5.2.9 maps over the totalizations | `GSets:Over.Totalization.equivalence` | done |
| Rem 5.2.10 equivariance | `GSets:Over.equivariant` | done |
| Def 5.2.11 G-subsets | `GSets:Over.SubG`, `underlying` | done |
| Ex 5.2.12 closed subsets | `GSets:Over.Subsets.equivalence` | done |
| Ex 5.2.13 pointed maps into the component | `StandardActions:Component.equiv` | done |
| Rem 5.2.14, Def 5.2.15 actions | `ActionComparison` | done |
| Ex 5.2.16 G abelian iff Ad_G = triv(UG) | `ActionExercises:AdjointTrivial.forth`, `back` | done |
| Ex 5.2.17 G trivial iff Ad_G = ℙ_sh | `ActionExercises:AdjointPrincipal.to`, `from` (trivial means BG contractible) | done |
| Def 5.2.18 finite G-sets | `GSets:Over.finite` | done |
| Def 5.2.20, Lemma 5.2.22 transitivity | `GSets:Over.Transitive`, `ConnectedActions:Family` | done |
| Lemma 5.2.23 injective evaluation | `GSets:Over.Evaluation.injective`, `path-evaluation-injective` | done |
| Ex 5.2.24 | — | open |
| Def 5.2.25 normal G-sets | `GSets:Over.isNormal` | done |
| Ex 5.2.26 evaluation is an equivalence everywhere | `ActionExercises:Evaluations.everywhere` | done |
| Def 5.2.28, 5.2.29 actions in a groupoid, standard action | `StandardActions:In.classify` ((BG → A) ≃ Σ_a Hom(G, Aut_A(a))), `standard` | done |
| Ex 5.2.30–5.2.32 | — | open |

## 5.3 Subgroups

| Item | Unit | Status |
| --- | --- | --- |
| Def 5.3.2, Ex 5.3.3, Def 5.3.4 | `Subgroups:Over.Sub`, `Action.At.group`, `underlying` | done |
| Lemma 5.3.6 Sub(G) is a set | `SubgroupTheory:Over.sub-set` | done |
| Def 5.3.11 decidable subgroups | `SubgroupTheory:Over.decidable` | done |
| Def 5.3.13 monomorphisms | `SubgroupTheory:Over.isMono`, `Mono`, `trivial`, `proper` | done |
| Lemma 5.3.18, Ex 5.3.20 Sub(G) ≃ Mono(G) | `SubgroupMono:Over.equivalence` (`E` is the preimage map) | done |
| Cor 5.3.21 Mono(G) is a set | `SubgroupMono:Over.mono-set` | done |
| Lemma 5.3.22 picked symmetries | `SubgroupMono:Over.Picks.to`, `from` | done |
| Def 5.3.23 trivial and proper subgroups | `SubgroupTheory:Over.trivial-sub`, `proper-sub` | done |
| Constr 5.3.27, 5.3.28 Lagrange | `SubgroupTheory:Over.Lagrange.construction`, `construction'` | done |
| Ex 5.3.29 Lagrange's theorem | `LagrangeTheorem:At.finite`, `theorem` (#G = #X · #H) | done |
| Example 5.3.17 product inclusions are monos | `ActionExercises:FirstInclusion.mono`, `SecondInclusion.mono` | done |
| Example 5.3.5 loops fixing 0 in R_m are loop^(mj) | `SubgroupExamples:Rotations.forth`, `back` (R_m via circle monodromy, m = n+1) | done |
| Example 5.3.7 (X, k) : Sub(Σ_(n+1)) has underlying group Σ_n | `SubgroupExamples:FixOne.At.identification` (transitivity proved, not assumed) | done |
| Ex 5.3.8 n-element sets ≃ pointed (n+1)-element sets | `SubgroupExamples:PointedFinite.equivalence` | done |
| Ex 5.3.9 A ≃ Σ_B (A ≃ B + 1) for decidable A | `SubgroupExamples:Complement.equivalence` | done |
| Example 5.3.14 A ↦ A + Y is a mono Σ_X → Σ_(X+Y) | `SubgroupExamples:SumMono.mono` | done |
| Ex 5.3.16 j ≠ j′ : C₃ → Σ₃ identified in Mono(Σ₃) | `SubgroupCyclic:C3Monos.different`, `identified` (j′ = j ∘ inversion) | done |
| Example 5.3.25 (G, i₁) = F(ℙ ∘ proj₂, refl) | `SubgroupExamples:ProductSubgroup.first` | done |
| Ex 5.3.30 Uℤ ≃ m × UH_m | `SubgroupExamples:RotationLagrange.equivalence` (explicit choice map, R_m transitive) | done |
| Ex 5.3.31 choice map for the free group on two generators acting on 3 | `SubgroupWedge:WedgeAction.choice`, `equivalence` (the wedge group of GroupSums; no groupoid assumption) | done |
| Examples 5.3.10, 5.3.19, Ex 5.3.15 | — | open |

## 5.4 Invariant maps and orbits

| Item | Unit | Status |
| --- | --- | --- |
| Def 5.4.1 action type, invariant maps, orbits | `Orbits:Over.Orbits.hG`, `invariant`, `quotient` (transitive G-subsets) | done |
| Def 5.4.3, Lemma 5.4.4 | `Orbits:Over.Orbits.cls`, `Class.transitive`, `orbit0` | done |
| Lemma 5.4.5 | `Orbits:Over.Orbits.surjective`, `effective`, `truncation` (‖X_hG‖₀ ≃ X/G) | done |
| Cor 5.4.6 | `Orbits:Over.Orbits.same-orbit`, `orbit-of-hit`, `orbit-onto` | done, except the factorization through the quotient set |
| Rem 5.4.7 SubG(X) ≃ (X/G → Prop) | `ActionExercises:SubsetsOfOrbits.equivalence` | done |
| Ex 5.4.8 X/G contractible iff X transitive | `ActionExercises:Over.Contractible.to`, `from` | done |
| Ex 5.4.12 same orbit gives ‖G_x = G_y‖ | `ActionExercises:Over.stabilizers` | done |
| Def 5.4.10 stabilizer and orbit | `Orbits:Over.Orbits.Stabilizer.group`, `inclusion`, `through` | done |
| Lemma 5.4.14 splitting into orbits | `Orbits:Over.Orbits.partition` | done |
| Def 5.4.15 fixed and free | `Orbits:Over.Orbits.Stabilizer.fixed`, `free` | done |
| Lemma 5.4.18 | `Orbits:Over.Orbits.Free.to-injective`, `from-injective` (via `to-loops`, `from-loops`) | done |
| Lemma 5.4.19 | `Orbits:Over.Orbits.set-free`, `free-set`, `set-orbit0`, `orbit0-set` | done |
| Lemma 5.4.20 fixed points | `Orbits:Over.Orbits.Fixed.to-fixed`, `from-fixed` | done |
| Lemma 5.4.21 invariant maps | `Orbits:Over.Orbits.Invariant.ev-injective`, `equivalence` | done |
| Def 5.4.25, Constr 5.4.28 orbit–stabilizer | `Orbits:Over.Orbits.OrbitStabilizer.tilde`, `theorem` | done |
| Cor 5.4.29, 5.4.30 | `Orbits:Stabilized.tilde-free`, `cosets` | done |
| Constr 5.4.31 | `Orbits:PreLagrange.equivalence` | done |
| Ex 5.4.23 Hom_G(X,Y) as fixed points | `ActionExercises:Maps.equivalence` | done |
| Ex 5.4.16, 5.4.17 (first two parts) | `ActionExercises:TrivialStabilizer.fixed`, `equiv` (BG_s ≃ BG); `PrincipalStabilizer.free` (BG_g contractible) | done |
| Ex 5.4.26 the action on G̃_x | `ActionExercises:TildeAction.acts` | done |
| Ex 5.4.27 (first two parts) | `ActionExercises:TrivialStabilizer.action-contr`, `PrincipalStabilizer.action-type` | done |
| Ex 5.4.17, 5.4.27 (third parts), 5.4.22, 5.4.32 | — | open |

## 5.5 Torsors

| Item | Unit | Status |
| --- | --- | --- |
| Def 5.5.1, Def 5.5.4, Thm 5.5.7 | `ConcreteTorsors:Classify`, `TorsorDelooping` | done |
| Ex 5.5.2 torsor iff free and transitive | `ActionExercises:Over.Torsors.to`, `from` (via contractible action type) | done |
| Lemma 5.5.6 | `InducedActions:Principal.embedding` | done |
| Def 5.5.9 restriction and induction | `InducedActions:Along.restrict`, `induce`, `unit` | done |
| Rem 5.5.13 coinduction | `InducedActions:Along.coinduce` | done |
| Constr 5.5.16 induced torsors | `InducedActions:Torsors.induce`, `square`, `pointed` | done |
| Lemma 5.5.17 | `InducedActions:Restriction.connected`, `Restrict.embedding` | done |
| Ex 5.5.11 | `ActionExercises:InduceIso.equivalence` (f_!X ≃ X ∘ Bf⁻¹ for an isomorphism f); `Adjunctions.Left.equivalence` (Hom_H(f_!X,Y) ≃ Hom_G(X,f^*Y)) | done |
| Ex 5.5.15 Hom_G(f^*Y,X) ≃ Hom_H(Y,f_*X) | `ActionExercises:Adjunctions.Right.equivalence` | done |
| Ex 5.5.10 f_! needs the set truncation | `ActionExercises:WhyTruncate.not-set` (ℤ → 1, constant 1) | done |

## 5.6 and 5.7

| Item | Unit | Status |
| --- | --- | --- |
| Thm 5.6.1 Cayley | `CayleyMono:Regular.rho`, `mono` (ρ_G : G → Σ_UG is a monomorphism); `Cayley:Regular.preserves` | done |
| Ex 5.6.4 fixed permutations of UG | `ActionExercises:FixedPermutations.fixed-hom`, `hom-fixed`, `eval-equiv`, `compose`, `inverse-equiv`, `inverse-hom` | done |
| Lemma 5.7.2 | `Burnside:Law.formula`, `sum-of-fixed-points` | done |
| Ex 5.7.1, Thm 5.7.3 (Fermat) | — | open |
