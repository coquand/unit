Generic finite chart-family and ideal-error assembly
====================================================

Status: mathematical construction complete, checked, uncommitted.
Only this new directory is edited; existing developments are relative
links. Four owned sources, 202 owned declarations. No new axioms/choice.

GenericChartFamilyAssembly.Single[A,setA,n,k].C
GenericChartFamilyAssembly.Pairs[A,setA,n,k].C
------------------------------------------------
The Single index is Fin n and face is GenericSubsetFaces.singleton n.
The Pairs index is GenericSubsetFaces.Pair n and face is pairSet n.
Their actual targets are GenericCech.Cochains[n,k,r], at cardinality r=1
and r=2 respectively. k is any integer, including negative twists.
No positive coordinate-count assumption is used; augmented n=0 semantics
remain exact, with no ordinary vertex or edge cochains at n=0.

For either wrapper C:
 .Local[i].C = GenericLaurent.Chart[Exp n,Sub n,constant NativeBad(face i,k)]
   This is the actual NativeDegreePart.Part[k].Into[Sub n] chart module.
 .P = dependent product of these local modules (ChartFamilyAssembly4.Product).
 .assemble : P.El -> CH.El, where CH is actual GenericCech.Cochains.
 .value f i m : val(assemble f)(face i)m = Local[i].C.val(f i)(face i)m.
 .linear : A-linear map from P.mod to CH.mod.
 .ext x y : equality at all indexed faces/exponents implies x=y.

General .Over[A,setA,n,I,face,r,card,classify,injective,k] takes an indexing
of exactly the cardinality-r faces. Single and Pairs supply these facts:
cardinality/classification are unchanged GenericSubsetFaces theorems;
GenericFaceInjectivity proves singleton/pair injectivity structurally.
There is no finite enumeration or cover parameter and no omitted
finiteness hypothesis. For each subset s, decide its cardinality. At the
right cardinality, classify s and read the corresponding local component;
otherwise put zero. FiniteChartChoice.finite-sub unions supports over all
Sub n inside truncation. This builds an ACTUAL global cochain. Vanishing
outside projective degree/chart support and wrong cardinality is proved.
The new vertex is first in the subset orientation, unchanged throughout.

GenericChartErrorAssembly.Single[A,setA,n,t,b,s,p,e,hpC,k].C
GenericChartErrorAssembly.Pairs[A,setA,n,t,b,s,p,e,hpC,k].C
-----------------------------------------------------------------
Here A is any commutative set-ring, b : Fin t -> A, p is the finite original
polynomial list in n ordinary variables, and hpC gives termwise projective
Hom(pos(e_q)), exactly the GenericReesChart API. X exponents are Fin n ->
Base.Nat; Laurent exponents are Fin n -> Int.

For either wrapper C:
 .J = GenericReesChart.Over[A,setA,n,t,b,s,p,e,hpC]
 .CJ = J.At[k,r]; .CS is the chart-family assembly above.
 .Local[i].Ideal = GenericChartIdeal over face i and index type Sub n,
   using J.hp-shift (constructed HomShift zero e from hpC).
 .Local[i].Q is its explicit image/J/I-power bookkeeping.
 .JFamily[x,h].witness : CJ.Q.JW(CS.assemble x)
   assembles every original J coefficient at its required shifted twist.
 .assembledWitness depth ws wi : CJ.Q.FC.Wit depth(CS.assemble ws)
   bundles local explicit ideal-power trees and maps them through linear.
 .Assemble[depth,x,ws,wi,rem] exports
   w         : CJ.Target.El
   ideal     : CJ.Q.FC.Wit depth w
   remainder : CJ.Q.JW(CJ.Q.ML.msub(CS.assemble x)w)
   error     : CJ.Q.IJW depth(CS.assemble x).

wi gives each Local[i].Q.FC.Wit depth(ws i), and rem gives each local
JW(x_i-ws_i). These are EXPLICIT data, no truncation or assumed realization.
GenericChartErrorWitness.Realize supplies them directly: instantiate its
polynomial homogeneity proof with J.hp-shift. Its source native-ring W
witness type is independent of that proof, so existing section native
witnesses are accepted unchanged.

The J proof is a finite coefficient sum: evaluate local equality at face i,
assemble each polynomial multiplier at k-e_q, use the polynomial action
coefficient formula and congruence, then global face extensionality. The
ideal proof reuses unchanged ProductIdealWitnesses.Over (pure dependent
module products) and IdealPowerWitnessTransport along the proved linear
assembly. Their four-coordinate file locations impose no dimensional
hypothesis: only their generic Product/Over instances are used.

Integration
-----------
The generic section agent consumes these APIs unchanged in checked
GenericSectionAssembly and GenericFiniteFibreSections, constructing actual
global sections, boundary ideal errors and compatibility witnesses from
residual data. This directory itself supplies the independent assembly
step, not the native geometric series or Rees correction.

Regressions
-----------
GenericAssemblyRegression proves arbitrary cochains vanish for the empty
coordinate vertex/edge complexes and the one-coordinate edge complex.
An explicit depth-one unit-ideal tree is built for arbitrary local input
families, bundled and assembled with a zero original-equation remainder.
Instances cover coordinate counts0,1,5 and negative twists. The section
agent separately checks nonzero native and global finite-fibre examples.
See VALIDATION.txt for all checks; .opens is a full measured unfolding
inventory, not an independently minimal allowlist.
