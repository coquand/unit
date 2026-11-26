# PLAN-QCOH-UA: Mod(A) = QCoh(Spec A) as univalent categories

Goal (2026-11-26). For a commutative ring A (a set), identify the univalent
category of small A-modules with the univalent category of quasi-coherent
module sheaves on Spec A, and transport structure across the identification:
the abelian structure (a property) and the symmetric monoidal structure of
the tensor product (data, laws are propositions since hom types are sets),
and cokernels without sheafification.

Motivation: Elinder, *Investigating abelian categories in univalent type
theory* (Chalmers MSc 2021, `~/CANONICITY/abeliancat.pdf`): RMod univalent
and abelian; future work §6.3.1 "a category equivalent to an abelian
category is abelian". Here the second category is geometric.

Constructive point: by `WeakCategoryEquivalence` (HoTT book Lemma 9.4.7), a
fully faithful functor out of a univalent category that is *merely*
essentially surjective is an equivalence, without choice. Classically one
chooses, for each quasi-coherent F, a module M with F = M~.

Template: `QcqsCategories.seg` (geometric vs functorial qcqs schemes:
FullSubcategory + fully faithful + mere ess. surj. -> WeakCategoryEquivalence[l+],
CategoryQuasiInverse[l+]; then FibreCategorySIPTheorem[l+] for equality).
Categories at Category[l+,l] are accepted where Category[l+,l+] is expected.

## Steps (worker in brackets)

1. [A] `SerreModuleUnivalent`: the precategory `SerreModuleCategory.Over[A].modules`
   is univalent (structure identity principle on `SerreModule.Module`;
   `FromEquiv` already gives the categorical iso from an underlying
   equivalence; template `GeometricCategory` via `Category.FromTotal`).
2. [B] `SerreModuleSheafCategory`: module sheaves on (L, G) and
   `Transform.Hom` form a univalent category (natural iso -> path by funext
   and the SIP on presheaf data). `SerreQCohCategory`: QCoh(X) = full
   subcategory on `SerreQuasiCoherent` (a proposition), univalent.
3. [C] The associated-sheaf functor M |-> M~ : Mod(A) -> QCoh(Spec A):
   M~ is quasi-coherent (one-chart atlas); functor laws from `SerreAssociatedMapLaws`.
4. [C] Fully faithful: Gamma(Spec A, M~) = M; a map M~ -> N~ is determined
   on basic opens by the universal property of localisation.
5. [C] Merely essentially surjective: F quasi-coherent, then F(D g) = Gamma(F)_g
   (`SerreAffineLocalisation`, Cor. 4.6) is the counit on basic opens;
   `SerreModuleSheafLocalEquivalence` extends it to all opens.
6. [D] Assembly: WeakCategoryEquivalence, CategoryQuasiInverse,
   FibreCategorySIPTheorem: Mod(A) = QCoh(Spec A). Transport: abelian,
   tensor with its coherence, cokernels = (coker)~.

Follow-up: descent, QCoh(X) for qcqs X as a limit of QCoh(Spec A_i).

## Status

(workers append dated checkpoints below)

2026-11-26 [A] step 1 DONE. `SerreModuleUnivalent.seg` (slot A in All.seg),
check: `ok SerreModuleUnivalent 91 declarations 0.10 s`. Exports, level l,
inside `Over (A : CRing)`: `category : Category[l+,l].Category` (pre =
`SerreModuleCategory[l].Over[A].modules`), `univalent`, the module SIP
`total-contr`, `Fd = SipGeneric[l].Fundamental[S.Module,LinEquiv,idLin,total-contr]`
(sip, idToIso, sip-equiv), `LinEquiv`, `ToLin`/`FromLin`/`round` (categorical
iso <-> linear equivalence), `Single[M].proposition`. Top level: `unop`
(a SipGeneric notion), `isSet-prop`. Route: modules = SipGeneric notion
point+binop+unop+action A.R with axioms (set + 8 laws); the categorical
singleton is a retract of the SIP total space; Category.FromTotal.

2026-11-26 [B] step 2 DONE. Four files (slot B in All.seg), check:
`ok SerreModuleLinearIdentity 63 decl 0.07 s`, `ok SerreModuleSheafIdentity
95 decl 0.13 s`, `ok SerreModuleSheafCategory 79 decl 0.26 s`,
`ok SerreQCohCategory 9 decl 0.09 s`; `segc sag/qcqs changed`: 507 modules OK.
- `SerreModuleLinearIdentity[l].Over[A]`: `LinearEquivalence M N = (f : linear
  Hom) * isEquiv f.fn`, `identity`, `Total`, `total-contr` (module SIP via
  SipGeneric binop+action with axioms; zero/neg unique, local copy of pn/AbAxioms).
  Independent of A's `SerreModuleUnivalent` (whose LinEquiv also has zero/neg);
  could be merged later.
- `SerreModuleSheafIdentity[l].On[L,G]`: `equivalence-total-contr E`
  (presheaves F with `SerreModuleSheafIso.Equivalence E F`), `sheaf-total-contr E`
  (module sheaves, `SheafTotal E = (F : ModuleSheaf) * Equivalence E.presheaf F.presheaf`),
  `sheaf-prop`; top-level `Semi[A,B,h,M,N].ext` (semilinear maps by fn),
  `SetSheaf[L,S].sheaf-prop`.
- `SerreModuleSheafCategory[l].On[L,G]`: `precategory : Category[l+,l].Precategory`
  (ob ModuleSheaf, `hom E F = Transform[E.presheaf,F.presheaf].Hom`, `idn` =
  IsoOps.Identity, `comp`, `at E F f a x`), `Arrow[E,F].ext/.set`, `univalent`,
  `category : Category[l+,l].Category`; `to-iso E F : Equivalence -> precategory.Iso E F`,
  `to-equivalence E F : Iso -> Equivalence`, `iso-again`, `equivalence-again`,
  `iso-equivalence E F : Pr.Equiv (Equivalence ..) (precategory.Iso E F)`.
- `SerreQCohCategory[l].On[L,X]`: `Sheaves`, `quasi-coherent`, `Sub`
  (FullSubcategory[l+,l]), `precategory`, `univalent`, `category` at Category[l+,l+].

2026-11-26 [C] steps 3, 4, 5 DONE. Four files (slot C in All.seg), check:
`ok SerreTildeGlobal 59 decl 0.24 s`, `ok SerreTildeFaithful 75 decl 0.28 s`,
`ok SerreTildeQuasiCoherent 52 decl 0.36 s`, `ok SerreTildeEssential 111 decl
0.87 s` (`segc sag/qcqs check` of the four + All: OK). Level l throughout; no
postulates, no new parameters. Spec A = `Affine[l].Over[A].spec` on
`ZariskiLattice[l].Over[A].lattice`; its sheaf is convertible with the
`AM.G.SH.structure` of `SerreAssociatedSheaf` (checked by use). No O(top)-vs-A
obstruction: `Global` gives a |-> a|top bijective, `d-global`, `extend-global`.
- `SerreTildeGlobal[l].Over[A,setA,Md]` (Gamma(M~) = M): `glob x` (components x/1),
  `global : Hom_A(Md, TopA.sections)` (M~(top) along a |-> a|top), `equiv`,
  `inverse`, `inverse-glob`, `glob-inverse`; lemmas `scale-section`,
  `extend-scale`, `restrict-section`, `restrict-scale`, `restrict-global`, `at-eval`.
- Step 3, `SerreTildeQuasiCoherent[l].Over[A,setA,Md]`:
  `qcoh : SerreQuasiCoherent[l].On[Z.lattice,GM.AF.spec,GM.Sh.associated].IsQuasiCoherent`
  (also `model`, `atlas` = one chart top; `At[s].lambda` for every s in O(top)).
  Route: lambda_(top,s) by clearing/killing along the square
  glob^-1 / eval_a against x |-> x/1 (ElementarySquare.Square, Unrestrict),
  then SerreLambdaCriterion at top (AffineQcqs.TestSpace affine).
- Step 4, `SerreTildeFaithful[l].Over[A,setA,Md,Nd]`:
  `forward u = SerreAssociatedMap[l].Over[A,setA,Md,Nd,u].morphism`,
  `backward`, `fully-faithful : Pr.isEquiv Lin.Hom Transforms.Hom forward`
  with `Lin = MM.Between[A,A,RH.identity A,Md,Nd]`,
  `Transforms = MS.On[Z.lattice,GM.AM.G.SH.structure].Transform[GM.S.presheaf,GN.S.presheaf]`
  (GM.S.presheaf = `SerreAssociatedSheaf[l].Over[A,setA,Md].associated.presheaf`).
  Top level `TransformExt[L,G,E,F].ext` (duplicates B's `Arrow[E,F].ext`; D may use either).
- Step 5, `SerreTildeEssential[l].Over[A,setA,F,qc]` with
  `F : MS.On[Z.lattice,Affine[l].Over[A].spec.sheaf].ModuleSheaf`,
  `qc : SerreQuasiCoherent[l].On[Z.lattice,Affine[l].Over[A].spec,F].IsQuasiCoherent`:
  `Gamma : SM.Over[A].Module` (F(top) along a |-> a|top) and
  `equivalence : SerreModuleSheafIso[l].On[Z.lattice,AF.spec.sheaf].Equivalence
  GM.Sh.associated.presheaf F.presheaf` (Gamma~ -> F), constructed ACTUALLY
  (no truncation left in the result; the mere atlas is eliminated into the
  proposition "lambda is an equivalence"). For D: preimage of F is
  (Gamma, SerreTildeQuasiCoherent.Over[A,setA,Gamma].qcoh) with iso
  B.to-iso _ _ equivalence; functor laws from SerreAssociatedMapLaws
  (Identity/Composite.morphism-at, pointwise) + an ext lemma.

2026-11-26 [D] step 6 DONE. `SerreQCohEquivalence.seg` (slot D; also imports the
generic FibreCategory{Equivalence,EquivalenceTransport,SIP,SIPFamily,SIPFixed,
SIPReindex,SIPTheorem,Adapter} files, previously only in FibreAll). Check:
`ok SerreQCohEquivalence 53 declarations 0.05 s`; `segc sag/qcqs changed`:
519 modules, 0 failed. Inside `Over (A : CRing) (setA)`: `Modules` (Mod(A) lifted
to Category[l+,l+] as FullSubcategory on `Trivial`), `QCoh = SerreQCohCategory.On
[Z.lattice,AF.spec]`, `functor` (laws IdLaw/CompLaw via SerreAssociatedMapLaws +
Arrow.ext), `fully-faithful` (C's, raised by `raise`), `split-surjective` (actual:
(Gamma F, tt) with Sh.to-iso of C's equivalence), `essentially-surjective`,
`object-equivalence`, `equivalence` (CategoryQuasiInverse), `fibre-equivalence`,
`equality : Id K.Category Modules.category QCoh.category`.
Next: [E] abelian transport, [F] monoidal transport (running).

2026-11-26 [F] symmetric monoidal transport DONE. Four files (slot F in All.seg), check:
`ok MonoidalCategory 26 decl 0.07 s`, `ok SerreTensorMonoidal 131 decl 0.75 s`,
`ok SerreTensorSymmetric 51 decl 0.30 s`, `ok SerreQCohMonoidal 9 decl 0.00 s`;
`segc sag/qcqs changed`: 525 modules, 0 failed. No postulates, no new parameters.
- `MonoidalCategory[k]` (C : Category[k,k].Category): `record Monoidal[C]` (tensor,
  tmap, tmap-idn, tmap-comp: bifunctor stated directly; unit; associator,
  left-unitor, right-unitor as C.pre.Iso with associator-natural, left-natural,
  right-natural; pentagon, triangle); `record Symmetric[C]` (monoidal, braiding,
  braiding-natural, symmetry, hexagon); `transport`, `transport-symmetric` (subst).
- `SerreTensorMonoidal[l].Over[A,setA]`: `monoidal : MonoidalCategory[l+].Monoidal
  [QE.Modules.category]` (QE = SerreQCohEquivalence.Over[A,setA]); `tensor`, `tmap`
  (SerreTensorMaps.Map), `unit` (regular module), `associator` (TensorAssociativity.At),
  `left-unitor` (TensorMaps.Unit), `right-unitor` (= RightUnit.iso: Swap then Unit),
  `Quad[W,X,Y,Z].Equal` (maps out of ((W(x)X)(x)Y)(x)Z agree on pure quadruples),
  law modules TmapIdn, TmapComp, AssocNatural, LeftNatural, RightNatural,
  Pentagon, Triangle (all laws proved on pure tensors).
- `SerreTensorSymmetric[l].Over[A,setA]`: `braiding` (TensorMaps.Swap), BraidNatural,
  Symmetry, Hexagon, `symmetric : MonoidalCategory[l+].Symmetric[QE.Modules.category]`.
- `SerreQCohMonoidal[l].Over[A,setA]`: `qcoh-monoidal : Monoidal[QE.QCoh.category]`,
  `qcoh-symmetric : Symmetric[QE.QCoh.category]` (transport along QE.equality).
- NOT done: the object-level description (M~ (x) N~ = (M (x) N)~ for the transported
  tensor). It needs coe (ap ob QE.equality) = on-objects, i.e. computing through
  FibreCategorySIPTheorem (Reindex by equivalence induction, pre-eta, pre-path-to-
  category); not cheap, skipped. (A generic J lemma "transported tensor of images =
  image of tensor" would be easy; the missing piece is the ob-action of equality.)

2026-11-26 [E] abelian transport DONE. Three files (slot E in All.seg), check:
`ok CategoryAbelian 55 decl 0.07 s`, `ok SerreModuleAbelian 130 decl 0.30 s`,
`ok SerreQCohAbelian 14 decl 0.09 s`; `segc sag/qcqs changed`: 526 modules OK.
No postulates, no new parameters, no choice.
- `CategoryAbelian[k]` (generic, Elinder §4.3-4.4 without Ab-enrichment):
  `isContr`; in `On[C : Category[k,k].Precategory]`: `IsInitial`, `IsTerminal`,
  `IsZero`, `Zero`, `Monic`, `Epic`, `Factors`/`factors-contr`/`monic-factors`,
  `Cofactors`/`cofactors-contr`/`epic-cofactors`, `Pairings`, `IsProduct`, `Product`,
  `HasProducts`, `Copairings`, `IsCoproduct`, `Coproduct`, `HasCoproducts`,
  `pairings-contr`, `copairings-contr`; `Zeros[z]`: `zero x y` (x -> z -> y),
  `IsKernel`, `Kernel`, `HasKernels`, `IsCokernel`, `Cokernel`, `HasCokernels`,
  `MonicsAreKernels`, `EpicsAreCokernels` (mere, Truncation[k]); record `Abelian`
  {zero, products, coproducts, kernels, cokernels, monics, epics}. Top level, over
  `K.Category`: `HasZero`, `HasKernels`, `HasCokernels` (Sigma with a zero object),
  `HasProducts`, `HasCoproducts`, `IsAbelian`; `Transport[C,D,e].move F x` (one subst).
  All are STRUCTURES (chosen data); propositionality not proved (not needed).
- `SerreModuleAbelian[l].Over[A,setA]` on `SerreQCohEquivalence.Over[A,setA].Modules`:
  `zero-module` (on Top), `zero`, `zero-at` (zero arrow is x |-> 0 by refl),
  `Ker[x,y,f].kernel` (KernelAlgebra), `Coker[x,y,f].cokernel` (SerreModuleCokernel),
  `kernels`, `cokernels`, `Pairs[x,y].product/.coproduct` (biproduct on the pair module),
  `products`, `coproducts`, `MonicKernel[s,a,m,mono]` (m injective since its kernel
  inclusion i has m i = m 0; m = kernel of coker projection, preimages by zero-image +
  injectivity), `monics`, `EpicCokernel[b,s,e,epi]` (e merely surjective since coker
  projection p has p e = 0 e; e = cokernel of its kernel inclusion, descended map from
  the propositional graph {v | merely x, e x = y, u x = v}), `epics`,
  `abelian : CategoryAbelian[l+].IsAbelian Modules.category`.
- `SerreQCohAbelian[l].Over[A,setA]`: `qcoh-abelian : IsAbelian QCoh.category`,
  `qcoh-zero`, `qcoh-kernels`, `qcoh-cokernels` (cokernels in QCoh(Spec A), no
  sheafification), `qcoh-products`, `qcoh-coproducts` (subst along QE.equality).
- NOT done: Ab-enrichment / additivity (by Freyd it follows; not formalised);
  object-level description of the transported cokernel ((coker u)~), same missing
  piece as for [F] (ob-action of `equality`); propositionality of the notions.

2026-11-26 [G] objects of transport DONE (object level). Three files (slot G in All.seg),
check: `ok FibreCategorySIPObjects 53 decl 0.11 s`, `ok FibreCategoryTransportObjects
33 decl 0.09 s`, `ok SerreQCohObjects 16 decl 0.10 s`; `segc sag/qcqs changed`: 529
modules, 0 failed. No postulates, no new parameters. Route: direct computation through
the SAME path `FibreCategorySIPTheorem.On[C,D,e].equality` (not an induction principle
for equivalences: each piece of the composite is one J or split lemma, so this was cheap).
- `FibreCategorySIPObjects[l]`: `ob-along` (subst of ob over precategories), `ob-trans`,
  `ob-eta`, `ob-eta-sym` (split), `ob-const` (ap to-pre O acts trivially, J),
  `ReindexOb[A].equality-ob` (Reindex.equality acts as e.1: subst-ob J, path-ob J with
  split base, UA.ua-beta), `obC C D p x = subst K.Category (\ X -> X.pre.ob) C D p x`,
  `obC-trans`, `obC-eta`, `obC-eta-sym`, `Sigma[X,u,x].sigma-ob` (J on the Sigma-eq path),
  `PrePath[C,D,q].objects` (pre-path-to-category acts as q), and
  `On[C,D,e].objects x : Id D.pre.ob (obC C D T.equality x) (e.forward.obj x)`.
- `FibreCategoryTransportObjects[k]`: `Along[C,D,p]`: `ob`, `hom` (arrows moved by J),
  `M[S].tensor x y : (transport p S).tensor (ob x) (ob y) = ob (S.tensor x y)`, `M[S].unit`,
  `Coker[H].object x y f : cokernel object of (hom f) in the moved HasCokernels = ob (coker f)`
  (all J, refl at refl); `Equivalent[C,D,e]`: same with F = e.forward.obj in place of ob
  (`M[S].tensor : moved.tensor (F x) (F y) = F (S.tensor x y)`, `M[S].unit`, `Coker[H].object`).
- `SerreQCohObjects[l].Over[A,setA]`: `objects M : obC .. QE.equality M = QE.on-objects M`;
  `tensor M N : QM.qcoh-monoidal.tensor (on-objects M) (on-objects N) = on-objects (TM.tensor M N)`
  (M~ (x) N~ = (M (x) N)~, about the EXISTING qcoh-monoidal); `unit` (= A~);
  `moved M N u` (= EQ.A.hom, u moved along the identification) and
  `cokernel M N u : (QA.qcoh-cokernels.2 (ob M) (ob N) (moved M N u)).1 = on-objects (Coker[M,N,u].object)`.
- OPEN: arrow level, `moved M N u = u~` (= on-arrows u, over the object paths). It needs the
  hom action of structure-equality (FibreCategorySIPFixed eqind on hom families with
  funext/ua) and of Reindex on homs; not attempted. So the cokernel statement is about the
  moved arrow p_* u at the moved objects p_* M, p_* N, not literally about u~ : M~ -> N~.
