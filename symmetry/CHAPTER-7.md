# Chapter 7 in Unit

Declarations are written `File:Module.name`. Abstract groups are the records `Group[l].Grp`. Unlike the book's Σ-type, these records carry both inverse laws. `AbstractGroups:book-equiv` compares the two. "Open" means that no Unit proof exists yet. The Rocq blueprint is `Formalization/AbsGroup/S02–S07`.

## 7.2 Monoids and abstract groups

| Item | Unit | Status |
| --- | --- | --- |
| Def 7.2.1 monoids | `AbstractGroups:Monoid`, `underlying-monoid` | done |
| Ex 7.2.2 lists under concatenation | `AbstractGroups:ListMonoid.lists` | done |
| Laws before Def 7.2.3 | `AbstractGroups:UnitLaws`, `AssocLaw`, `MonoidLaws`, `InverseLaw`, `GroupLaws`, `LawProps` (each law is a proposition) | done |
| Def 7.2.3 type of abstract groups | `AbstractGroups:BookGroup`, `book-equiv : Grp ≃ BookGroup` | done |
| Rem 7.2.4, Lemma 7.2.5 inverses from mere inverses | `AbstractGroups:Inverses.contractible` (fibres of left multiplication over e), `unique` (contractible type of inverse operations) | done |
| Rem 7.2.7 isomorphisms | `AbstractGroups:Iso`, `iso-path` | done |
| Ex 7.2.8 the analysis | `AbstractGroups:Identity.equivalence : (J = K) ≃ Iso J K` (`idtoiso` is an equivalence) | done |
| Ex 7.2.9 opposite group | `AbstractGroups:op`, `op-iso`, `op-path` | done |
| Ex 7.2.10 conjugation | `AbstractGroups:Conjugation.preserves`, `iso`, `path` | done |
| Ex 7.2.12 e = g⁻¹g, g = (g⁻¹)⁻¹ | `AbstractGroups:Facts.left-inverse`, `inv-inv` (also `inv-mul`, `inv-e`, cancellation) | done |
| Ex 7.2.13 monoids and groups form groupoids | `AbstractGroups:monoids-groupoid` (via `MonoidIdentity.equivalence`), `groups-groupoid` | done |
| Ex 7.2.14 sheargroups | `AbstractGroups:Shear`, `shear-equiv : Grp ≃ Shear` (with `FromShear.bar-bar`) | done |
| Ex 7.2.15 Furstenberg groups | `AbstractGroups:Furstenberg`, `furst-equiv : Grp ≃ Furstenberg` | done |

## 7.3 Abstract homomorphisms

| Item | Unit | Status |
| --- | --- | --- |
| Ex 7.3.1 unit and inverses are preserved | `AbstractGroups:hom-unit`, `hom-inv` | done |
| Def 7.3.2 abstract homomorphisms, abstr on homomorphisms | `AbstractGroups:Hom`, `hom-set`, `abstr` | done |
| Rem 7.3.3 monoid homomorphisms, footnote example | `AbstractGroups:MHom`, `mult-not-unit` (the map 𝟙 → (Bool, and) at false) | done |
| Ex 7.3.4 composition, abstr(id), abstr(f₁f₀), endomorphism monoids | `AbstractGroups:hom-comp`, `hom-id`, `abstr-id`, `abstr-comp`, `endo-monoid`, `ConcreteEndo.monoid` | done |
| Ex 7.3.5 conjugation homomorphism and transport | `AbstractGroups:conj-hom`, `ConjugationPath.post`, `pre`. Here the path is `iso-ua`, the inverse of `idtoiso` | done |
| Ex 7.3.5 abstr(Binn)(g) = conj^g | — | open |
| Ex 7.3.6 pointwise products and abelian groups | `AbstractGroups:pointwise-hom`, `pointwise-abelian` | done |

## 7.4 Groups and G-sets, abstract to concrete

| Item | Unit | Status |
| --- | --- | --- |
| Def 7.4.1 abstract G-sets, principal torsor, torsors | `AbstractActions:Perm` (permutations as equivalences under ∘), `GSet`, `principal`, `AbsTorsor`. `MakeGSet` builds a G-set from an action | done |
| Ex 7.4.2 left and right principal G-sets | `AbstractActions:right-principal`, `left-right` (via `GSetPath.path`: an equivariant equivalence identifies G-sets) | done |
| Defs 7.4.4–7.4.7 (concr, q_G) | Partly covered by `TorsorDelooping` and `AbstractRecovery`, but not yet indexed item by item | partial |
| Thm 7.4.8 abstr is an equivalence | `GroupIdentity:equivalence` | done |
| Def 7.4.10 φ^* | `AbstractActions:pull` | done |
| Def 7.4.11 φ_! | `AbstractActions:Induce.gset`, `induce` (quotient of T × X by `Induce.rel`) | done |
| Ex 7.4.12 ∼ is an equivalence relation, respected by h, giving a homomorphism | `AbstractActions:Induce.rr`, `rs`, `rt`, `respects`, `move-mul`, `move-e` | done |
| Ex 7.4.14 φ_! ⊣ φ^* | `AbstractActions:Induction.equivalence` | done |
| Def 7.4.13 maps of G-sets | `AbstractActions:GHom` (function equality as in the book), `ghom-path`, `equivariant` | done |
| Identity principle for G-sets | `AbstractActions:GSetIdentity.equivalence : (X = Y) ≃ GIso X Y`, `GSetIdentity.path` | done |
| Def 7.4.15 φ_* | `AbstractActions:Push.C`, `push` | done |
| Ex 7.4.16 φ^* ⊣ φ_* | `AbstractActions:Coinduction.equivalence` | done |

## 7.5–7.7

| Item | Unit | Status |
| --- | --- | --- |
| Lemma 7.5.1 | `ChapterSeven:OrdinaryMaps.comparison` | done |
| Ex 7.5.2 (1) φ_! ℙ_G = ℙ_H | `AbstractActions:InducedPrincipal.iso` ((t,x) ↦ tφ(x)), `path` (an identification, since the quotient is small) | done |
| Ex 7.5.2 (2), Thm 7.5.3 | — | open |
| Lemma 7.6.1 | `ActionComparison:Classify.equivalence`. At one universe level its abstract G-sets are `AbstractActions:GSet (abs G)` definitionally: `ActionEncodings:Link.same`, `evaluation`, `action` (the action is transport) | done |
| Ex 7.6.2, Lemma 7.6.3 | — | open |
| Ex 7.6.4 the square for f^* | `ActionPullback:Square.square`, restated with `AbstractActions:pull` as `ActionEncodings:PullbackSquare.square` (with `Transport.path`: an identification of sets intertwining two actions identifies the abstract G-sets) | done |
| Ex 7.6.5 the square for f_! | — | open |
| Defs 7.7.1–7.7.2, Ex 7.7.3, first half of Ex 7.7.5 | `Heaps` | done |
| Ex 7.7.4 the group of symmetries r ↦ pq⁻¹r, and both endpoints | `HeapExercises:Shifts.grp`, `HeapShifts.end-group`, `end-iso` (end shape), `start-group`, `start-iso` (start shape, using r ↦ rq⁻¹p) | done |
| Ex 7.7.5 abelian heaps have purely isomorphic endpoint groups | `HeapExercises:AbelianHeap`, `AbelianEnds.iso`, `ends` (identification of the concrete endpoint groups) | done |
| Ex 7.7.6 | — | open: this amounts to a heap version of Thm 7.4.8 |
