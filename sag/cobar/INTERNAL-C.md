# The presheaf layer with C internal to the base: design note for the minimal route

canonicity-45, 2026-11-11.  Source: jonas.pdf Assumption 2 and §3.1-3.2 (the
Grothendieck construction, "Assumption 1 on the base descends to C"), §4, §6.
Requested by canonicity-4e after the user's ruling: do not rebuild the
full C-level layer; define the generic model G concretely over the total
category of C and check the SAG axioms for it, duality first.

## 1. The site, and whether the base stack instantiates at it

**The base stack is generic in its site.**  `core/CBase.seg` defines the
record `CB`: a V-coded small category (obV, homV, idH, compH, strict laws),
an interval OBJECT `Iv` with end points `ptH X e : Hom X Iv` natural in X,
connections, and a sieve classifier `Phi` (pre, Lands a proposition and its
laws, emptyS, topS, the point sieves `ptS e : Phi Iv` with lands-pt /
pt-lands / pt-disj, decidable `allS`, finite unions `bigU`, and `forallS`
along interval lines, on families of sieves `PhiL`).  `PosFull[a].PB` is
its instance at the posets, and EVERY file of core (lines, fillers,
compositions, the fibrant CwF with Sigma / Pi / Id / Glue / the universe,
FibNF, FibContr, FibHt, FibS3, CHSub, CHFibCart, CCart, CMove, ...) takes
the base only through PB.  So the question has a positive answer in
principle: give `CB` at the total category of C and the whole fibrancy
stack, the CwF of fibrant types and the contractibility / equivalence facts
of the bridge exist there, with "uniform in C" being ordinary fibrancy
(the vertical maps are maps of the site).

**The internal category, as data (record IC).**  C internal to the poset
base is, externally, for each base object I a small category C_I with
V-coded objects and morphisms, for each base map u : J -> I a restriction
functor u^* : C_I -> C_J, strictly functorial in u (id^* = id, (uv)^* =
v^* u^*) and preserving identities and composition strictly, and (for the
interval, below) a terminal object t_I of each C_I with u^* t_I = t_J.
Strictness is exactly the paper's: an internal category in cSet is a strict
category object, externally a strict functor from the base to Cat.

**CB at the total category (GrothCB).**  Objects (I, x), x in C_I;
Hom((J, y), (I, x)) = Sigma (u : Hom J I) Hom_{C_J}(y, u^* x), V-coded as
a SigV; id = (id, id); (u, f) . (v, g) = (uv, v^* f . g); the laws from the
base's and IC's strictness.  Interval: Iv := (Iv_base, t), so that
Hom((I, x), Iv) = Sigma (u : Hom I Iv_base) Hom(x, t) with the second
component unique (terminal): ptH, ptH-nat, the connections and their laws
are the base's on the first component, uniqueness of the second gives
lands-pt.  Sieves: Phi (I, x) := Phi I, pre along (u, f) := pre along u,
Lands through the projection; empty / top / point sieves, bigU, allS by
projection.  forallS X L for L : PhiL (I, x): every map into (I, x) factors
as a cartesian map (u, id) after a vertical one (id, f), and PhiL's own
naturality says that L at (u, f) is L at the cartesian lift (u, id)
restricted along the vertical part, where pre is the identity; so
forallS (I, x) L := forallS_base I (L at the cartesian lifts), and
lands-forall / forall-lands are the base's.  Estimate 400-700 lines, all
fields by projection; canonicity-c2 has offered to write it.

**The slices, for the levelwise notions (SliceCB).**  The paper's
"levelwise" (U : PSh(C) -> PSh(C0), levelwise fibrant / trivially fibrant /
equivalence) is fibrancy of the restriction of a type to the cartesian maps
over a point: at (I, x), to the slice category of the base over I, through
the functor (J, u : J -> I) |-> (J, u^* x), w |-> (w, id).  The slice is
itself a CB-site: interval (I x Iv_base, pr1) (the base's cylinder), whose
maps from (J, u) are the maps J -> Iv_base; sieves Phi (J, u) := Phi J, the
point sieves pulled back along pr2.  Estimate 300-500 lines, plus 300-500
for the two site functors (slice -> total, total -> base) and the pullback
of presheaves, types and fibrancy structures along a functor of sites (one
generic module).  With this, "levelwise fibrant", "levelwise equivalence"
and "fibrant over the total category" are ONE definition (CB-fibrancy,
CEquiv.EquivOp) at two sites, and the levelwise inputs of Lemmas 12, 14,
16 and Prop 13 are stated in the base's own vocabulary.

**Slice versus total, decided per use.**  Total category: everything
global (contexts, types, fibrancy, Sigma / Pi / Id, D, the equivalences
asserted by the axioms).  Slices: only the levelwise HYPOTHESES (the input
of Lemma 12; the levelwise equivalence of Prop 13 / Prop 17; Lemma 14's
output "tau is a levelwise equivalence").  D's own definition needs a third
notion, "vertical maps at a fixed stage" (chains in C_I), which IC gives
directly.

## 2. The concrete presheaves the axioms mention

With the ruling T = id (sag-model README), PSh(C)_DT is PSh(total)_D.

- **Pr**, the context of presentations: at (I, A), the kappa-presentations
  over the model A at stage I; **G0** (Remark 46): at (I, A) the fibre A
  itself; both given by IC and Tier 1 (sag/duality, syntactic
  presentations after the 2026-11-10 ruling).
- **G := D(yo F1)** (Construction 45): yo F1 is representable over the
  total category, hence a strict presheaf; D of it is a presheaf with a
  T-model structure (Lemma 43: D . yo preserves finite products up to
  levelwise equivalence; concretely the operations of F1 give the
  operations of G by functoriality of D . yo, and the equations hold up to
  paths, which is all a T-model structure asks).  Fibre at (I, A): by
  Lemma 14, tau : yo F1 -> G is a levelwise equivalence, so G(I, A) ~ Mod(F1,
  A) ~ A.
- **<u> := D(<u>_syn)**, where <u>_syn over Pr is the STRICT presheaf of
  syntactically presented G0-algebras (terms over A and the generators of
  u modulo the congruence; strictly functorial in A because substitution
  of terms is).  <u>_syn is levelwise a T-modal h-set, so D of it is
  fibrant (Lemma 12) and D-modal (Lemma 16), with fibre ~ <u>_{T/A}
  (Lemma 14).  This replaces the paper's free G-algebra in the inner model
  (which would need HITs there) by the modal replacement D of a concrete
  strict presheaf: the same object up to equivalence, by Lemma 52.
- **Sp(<u>) := Sigma (r : Mod_T(<u>, G)) (r . h ~ id)** and **G^Sp := Pi
  Sp G**, formed in the fibrant CwF over the total category (Sigma, Pi,
  Id, hom-types of T-models as Sigma / Pi / Id).  D-modal: Sigma / Pi / Id
  of D-modal types are D-modal (generic for any reflective subuniverse,
  once tau has its universal property; or Lemma 11's product half).
  Fibres: Lemma 54 (U preserves Pi with small domain), Lemma 59 = Lemma 72
  (proved generically in duality-presheaf), Prop 58 (Sp locally homotopy
  representable, Constructions 55-57).
- **N_D := D(Delta N)** for Axiom 3, fibres by Lemma 14.

Fibrancy is needed only of these (and of the D-images: Lemma 12).

## 3. What "the axiom holds in the model" requires

**Axiom 2 (Theorem 62).**  (a) <u> and G^Sp are fibrant and D-modal (above).
(b) Prop 17: a levelwise equivalence between D-modal types is an
equivalence: by Prop 13 (D of a levelwise equivalence is an equivalence)
and the naturality square of tau, 2-out-of-3 (generic, CEquiv at the total
site).  (c) The evaluation map ev : <u> -> G^Sp is a levelwise
equivalence: this is sag/duality's content at the fibres (Tier 1) through
the fibre identifications of §2 (Lemma 14, Lemma 54, Lemma 59, Prop 58):
Tier 3 / Tier 4 of DUALITY.md.  (a) and (b) are the new concrete content;
(c) is where the present semantic premises live.

**Axiom 3 (Theorem 61).**  The same with N_D, lambda pi_1 and Lemma 14.

**Axiom 1 (Prop 76).**  Local representability of Sp (Prop 58) and the
generic Prop 76 (Tier 6, checked conditionally), over the total category.

## 4. Which general results are then used, and which are dropped

Used: Lemma 12 (D preserves fibrancy; its output is now a single
fibrancy structure over the total site, the former "uniform half" being
part of it), Lemma 14 (tau levelwise equivalence: fibres of D X), Prop 13
(D of a levelwise equivalence), Cor 15 and Lemma 16 (tau_{D X} an
equivalence: D-modality of D X, needed for G, <u>, N_D), Prop 17 (generic
from Prop 13), Lemma 54, Lemma 59 (= 72, done), Prop 58, Prop 76 (done
conditionally); Sigma / Pi / Id of the fibrant CwF over the total category
(free from core at GrothCB); modality of Sigma / Pi / Id (generic).

Dropped: Theorem 29 as a statement about ALL types (the DescentOp record;
only desc2 at the three specific types is used, and desc1 only inside Lemma
16's proof), Lemma 11 (unless chosen for modality of Pi), the uniform-fibrancy
layer and the bridge (CPshContr / URel / FibC / S3C / NF / InvC: replaced by
FibContr, FibHt, FibS3, FibNF at the total site), CPshPi* (replaced by
fibPi at the total site), part (B), Prop 34's C-level truncation beyond
what c2's design keeps.

## 5. What carries over, what is rewritten, sizes (lines of .seg)

Unchanged: core (PosFull and all of CB's clients), the generic CwF files
(CwF*, SwanId, FibId*, PosIdY*, CwFQP, CwFKrInv, CwFPth), duality-presheaf
and duality-levelwise (generic in the CwF), the V-code tools c2 listed
(PiNat's top-level lemmas, IdV-ext, eqs3-cong).

Rewritten on the new index (same proofs, one more stage index; the
C-uniformity halves disappear into the site):
- Chains / Weights (weights are base-level and carry over; chains become
  chains at a stage with the cartesian action) and Cobar's D with tau, D on
  substitutions and elements (CPshDSub): 1,200-1,500.
- Lemma 12 (Lemma11L's Psi, Lemma12's inductive extension, CMove at the
  new site): 900-1,200.
- Lemma 14, Prop 13 (with Prop13U absorbed), Cor 15, Lemma 16 (the zig-zag
  lines are base lines at the total site: FibNF's LineY directly, no
  C-level LineYC): 2,000-2,500.
- Prop 17 and modality of Sigma / Pi / Id: 400-700 (generic in the CwF).
- Lemma 54 at the total site (c2): 500.
Replaced by core at the new site (no port): CPshC, CPshL, CPshExt, CPCwF,
CPshUFib, CPshSig*, CPshId*, CPshIdJ*, CPshJNatT, CPshPi*, CPshFillU,
CPshContr, CPshURel, CPshFibMaps, CPshIdExt, CPshFibC, CPshContrC, CPshFvC*,
CPshS3C, CPshNF*, CPshMapC, CPshInvC, CPshDT, CPshMapSub, CPshUTrivSub,
CPshEqSub, CPshDesc, CPshL16U, CPshEtaNat (they stay as the constant-C
case).
New: IC, GrothCB, SliceCB, the site functors and pullbacks: 1,000-1,700.
The concrete objects of §2 and the assembly of §3: 1,500-2,500 for G, <u>,
Sp, G^Sp, N_D and the axioms from the levelwise premise; Prop 58 and
Constructions 55-57 over the total site, if proved rather than assumed,
2,000-3,000 more.

Total for Axiom 2 with the fibre computations as premises: about
7,000-10,000 lines; the model-theoretic part (the site, D, Lemmas 12-16,
Prop 13, Prop 17) about 5,500-7,000 of them.  Axioms 3 and 1 afterwards:
500 and 300.

## 6. The one thing this route cannot make concrete

The internal category C of Construction 39 (kappa-presentable T-models in
h-sets of cSet) externalises to C0(I) = presentations by small types AT
STAGE I and C1 = maps of models over the slices: its objects and morphisms
are presheaf-level constructions (free models and quotients of h-sets over
the slices), which Tier 1 (sag/duality) only provides INTERNALLY, Unit being
read as the internal language.  Building C concretely would mean redoing
Tier 1 as presheaf constructions over the slices (cubical quotients /
HITs), out of scope.  So IC (C with its strict laws and terminal object), G0,
Pr, <u>_syn and the levelwise equivalences of Tiers 1 and 3 enter as the
fields of one record (the "concrete site" premise), and the layer proves
the axioms for every instance.  The gain over DUALITY.md's present
premises is precise: the whole of S2 (D, tau, Fib, IsEqT, D-eq, DT-fib,
Modal, isoT, restr-eq / post-eq, which c2 found uninstantiable with El :=
CEl) disappears, replaced by the concrete D over the total site and the
proved Lemmas 12-16 / Prop 13 / Prop 17; the premises left are Tier 1's
fibre computations and Tier 3's Lemma 54 / Prop 58 (or their proofs).

## 7. Minimal list of results, in dependency order, and a split

0. IC (record), GrothCB, SliceCB, site functors and pullbacks.  [c2: GrothCB,
   SliceCB; 45: IC and the pullback module]
1. Representables over the total site; Pr, G0, <u>_syn, N as presheaves
   from IC and the premise record.  [45]
2. Chains and weights at a stage; D on contexts / types / substitutions /
   elements, tau; D of a representable.  [45]
3. Lemma 12.  [45]
4. Lemma 14, Prop 13, Cor 15, Lemma 16.  [45]
5. Prop 17; modality of Sigma / Pi / Id (reflective-subuniverse argument
   from desc2 at the type, or Lemma 11's product half); Lemma 54.  [c2]
6. G, <u>, Sp, G^Sp; their fibrancy and D-modality; Axiom 2 from the
   levelwise premise.  [45 with c2 on Sp / G^Sp]
7. N_D and Axiom 3; Prop 58 and Axiom 1 (c2's Prop 34 design stays, re-based
   on this layer, for the truncation).
Nothing of 0-7 is started; the first code is IC and GrothCB, since every
later size depends on whether CB's fields go through by projection as
claimed in §1.
