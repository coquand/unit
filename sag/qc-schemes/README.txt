SAG Section 7.1 — worker A
=========================

Checked: scheme boundedness for mere witnesses; fraction-level representation
for 7.1.2; 7.1.8 on schemes and their open subtypes;
7.1.9–7.1.12; and 7.3.6 from Loc, SQC, Z-choice and fibrewise weak quasi-coherence.
There is no separate Restriction hypothesis in the final 7.3.6 statement.

All new sources are here. Sections 2–5, bridge7/, and torsor/ are imported
through read-only links and were not edited. No checker change, new axiom,
or quotient construction. Nothing committed.

Scheme boundedness
------------------
SchemeUniform[l].Over[R,setR,axioms].At[X,scheme,P,prop,up].theorem
  : ((x:X) -> ||Σn. P x n||) -> ||ΣN. (x:X) -> P x N||.
Here P is proposition-valued and upward closed under CoefficientBound.le.
The functions corollary bounds f:X->Nat. Local choice gives actual witnesses
on affine charts, affine boundedness bounds their indices, and finite choice
combines the chart bounds. No witness is chosen at every point of X.

Fraction-level 7.1.2: exact scope
-------------------------------
We do not construct a localized module M_f or assert an equality of module
types. The following is a checked statement about fractions, sufficient for
7.1.8; it does not assume weak quasi-coherence. 7.1.2 itself, as a
linear equivalence, is cokernel7/Localisation712.

FractionSections.Over[R,setR,axioms].At[X,scheme,M,setM,step,T,setT,fraction]
   .Laws[raise,detect] is a general theorem for any family of sets representing
   fractions. Its explicit inputs say that raising numerator and denominator
   preserves a fraction, and equal fractions at the same denominator have
   numerators equal after some number of steps. These are theorem parameters,
   not postulates about modules. Section[t].theorem turns pointwise mere
   representations of t into a common denominator and a global numerator.
   Equal[u,v,k,j,p].theorem supplies a uniform cross-multiplication exponent.
   This is the end-to-end representation argument, without a chosen M_f.

Internally, Iterates handles raising denominators, LocalSections bounds
annihilating exponents on the scheme overlaps and scales numerators, and
SectionDescent glues compatible sections of a set family by unique choice.
The proof uses finite choice over chart pairs, not choice over base points.

Module interface and 7.1.8
-------------------------
Worker B's Module is Alg73.Mod over RingBridge.ring R setR. We use it unchanged.
ModuleFractions relates multiplication powers to Iterates, translates the
natural-number indices, and derives the fraction representation/detection
laws on D(g) from the two clauses of WeaklyQC for a single module.

Restriction718[l].Over[R,setR,axioms].At[X,scheme,Mx,w].theorem-7-1-8
  : Modules[l].Over[R,setR].Restriction X Mx,
where w : Modules[l].Over[R,setR].WqcBundle X Mx.

The representation clause applies FractionSections with T(x) = (unit(g x) -> Mx).
The zero clause applies SchemeUniform to Kills. Thus both clauses use only
fibrewise WeaklyQC and the existing full SAG axiom bundle.

Restriction718...Open[X,scheme,Mx,w,sub,op].theorem gives the full open-subtype
form for U = Σx. sub x. U need not be affine. Its schemehood follows from 5.4.

Final 7.3.6
-----------
AffineVanishing[l].Over[R,setR,axioms].Torsors[X,Mx,w,T,ts] exports
  presented A fp e
  affine aff
  small-affine aff
with the same affine notions as worker B's Theorem736. Each proves
||(x:X) -> T x||. The only module hypothesis is w : WqcBundle X Mx;
Restriction is proved by 7.1.8 and supplied internally to Theorem736.
This is affine vanishing for torsor sections, in the existing torsor encoding.

7.1.9–7.1.12
-------------
BundleOperations.Over[R,setR,axioms].Sections[X,scheme,Mx,w].theorem-7-1-10
proves WeaklyQC (Modules.pi X Mx) for EVERY scheme X. Restriction718 at a
constant scalar gives the two clauses after swapping the section arguments.
The paper states 7.1.10 only for affine X, but uses it in 7.1.12(b) on fibres
that need only be schemes. The stronger checked statement closes that gap.

BundleOperations also defines inverse and direct (7.1.11), with the latter
a dependent product over the actual fibre. inverse-qc and direct-qc prove
7.1.12. Inverse image needs no scheme assumptions; direct image uses the
schemehood of fibres from 5.6.4 and the scheme version of 7.1.10.

RegularQC proves WeaklyQC R: choose a presented localization R_g, use its
SQC equivalence to represent functions on D(g), and apply LocalizationFractions
and LocalizationKernel. Their powers are translated to Alg73's natural numbers.

AlgebraQC.Over[R,setR,axioms].module-structure A equips an R-algebra A with
its underlying R-module, scalar multiplication r*a = iota(r)*a.
theorem-7-1-9 A fp proves its WeaklyQC. The proof takes a shorter route than
the paper's tensor argument: 7.1.10 gives WeaklyQC (Spec A -> R), and SQC's
canonical evaluation equivalence preserves zero and scalar multiplication.
QCTransport transfers the two fraction clauses along that equivalence.
The bundle corollary is pointwise and needs no condition on the indexing type.

This proof of 7.1.9 uses the full SAG bundle through 7.1.10; the paper's
SQC-only tensor argument and its smaller assumption list are not reproduced.
Neither a general module tensor product nor module localization is constructed.

BundleExamples instantiates 7.1.9 at the base algebra, proves that functions
on any scheme are weakly quasi-coherent, and tests inverse and direct images.
An empty fibre gives the zero module, while the identity fibre keeps 1 distinct
from 0; a false claim collapsing that direct image is rejected.

Checks
------
Direct seg All.seg, no --only or checking server:
  6568 declarations, 0 failed, 1.93 s.
  22 expected #fails rejections (19 imported, 3 new).

QCExamples covers empty schemes, empty open subtypes, a fraction system
requiring a positive scaling exponent, and the fact that 0^0 does not kill 1.
Two negative tests reject zero-exponent annihilation and equality of the
unscaled numerators 1 and 0. This entry point imports worker B's bridge but
does not import the unrelated gluing examples; counts differ accordingly.

Not done here
-------------
M_f as a quotient/module; an equality of localized module types in 7.1.2;
7.1.6 and 7.1.13 (worker B owns these); the general module tensor map in
Remark 7.1.3. notes/sag.tex documents the new results and the strengthened
7.1.10 statement. Worker B's SEC7-INTERFACE.md was not edited; HANDOFF-A.txt
provides the checked API for integration.
