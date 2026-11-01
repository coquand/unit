Homology on finite internal semi-Segal data (2026-11-01)
======================================================

This root rebuilds the internal categorical interface from finite
semi-Segal data. The existing homology theorem files are relative links
to ../hcat and check against this interface, including the sphere results.
The original hcat root and all of its .seg files are unchanged.
The finite semi-Segal inputs are now the adopted axiomatic foundation
for continuing homology here. Constructing a model is a separate task.

From unit/:
  ./segc sag/hcat-segal changed
  ./segc sag/hcat-segal all
  ./segc sag/hcat-segal stop
A fresh check is seg sag/hcat-segal/All.seg --opened.
Follow ../hcat/HANDOFF.md and the repository's seg/WRITING.md for
writing/checking rules.
Do not edit a linked file without considering its use in the original root.

What the foundation proves
--------------------------
Composition.hcomp is the long edge of the centre of horn2.
Associativity.hcomp-assoc is the missing triangle of the canonical horn3.
SemiSegalPentagon.pentagon fills a canonical Lambda^4_1 horn and reads
its missing tetrahedron. It has the exact existing HcompPentagon.Pentagon
type, interpreted with these NEW operations. No hpent or k5 is assumed.
Homology.WithPentagon.hpent is now a DEFINITION using this theorem.

SemiSegalNormalize proves fibrewise equivalences for the normalizations:
  raw triangles ~ paths from the selected composite;
  raw tetrahedra ~ equality of the two triangular pastings.
SemiSegalTetrahedra proves contractibility of normalized 3-horn fillers.
The degree-4 input is a family over all full boundaries, with contractible
horn fillers. It is not a parameter consisting of a pentagon equation.

Inputs and scope
----------------
Theory still takes univ, images, surjections; fe is derived.
SemiSegal takes an index type Cat, object and arrow families, identity
edges, cell2/horn2, cell3/horn3, cell4/horn4, and two unit triangles.
The index Cat here carries NO ambient functor-category structure.

The presentation is normalized in stages: cell3 is over normalized
triangle boundaries; cell4 is over normalized tetrahedron boundaries.
The normalization equivalences are proved. Unit laws follow from the
two unit triangles. Full degeneracy structure, completeness and Rezk
univalence are not required or asserted by this presentation.

The copower, zero-object, suspension, stability and sphere parameters
are the same kinds of universal-property inputs as in hcat. No new axioms
were added to the original root. The adopted finite semi-Segal
inputs are explicit parameters; they have NOT been constructed from
the original ambient Sattler-Warn parameters.

Checked reused development
-------------------------
Copowers, tensor maps, homotopy invariance, dimension, additivity, Fubini;
excision; the existing group constructions; positive-degree Mayer-Vietoris
with one structural boundary and all three repeating exactness positions;
reduced suspension; the existing sphere calculations.

The theorem SOURCES are unchanged. Equality with the groups/maps built
using the old categorical operations is not asserted. The old development
remains available separately. Its hpent is still assumed.
Sphere comparisons retain their existing set-level scope.

New homology results
--------------------
Homotopy and equivalence invariance in every nonnegative degree;
group isomorphisms induced by equivalences in every degree; compatibility
with commutative squares of maps of types. The group units in every
degree equal the class of the categorical zero, and hmap preserves them.

The positive Mayer-Vietoris sequence now joins a tail of groups
  H_1(B)*H_1(E) -> H_1(X) -> H_0(C) -> H_0(B)*H_0(E) -> H_0(X).
All arrows are homomorphisms. Exactness holds at H_1(X), H_0(C), and
at H_0(B)*H_0(E), with final difference u_* pr1 - v_* pr2. The final boundary
is the direct boundary at unitD, with the same incoming degree-one
difference as the positive sequence. No surjectivity onto H_0(X) is
claimed. Degree-zero induced maps now preserve multiplication, by the
naturality of the existing stable loop equivalence. Thus inclusion and
difference in degree zero are homomorphisms and the product position is
exact as image = kernel. BoundaryAdditivity proves additivity of the
existing final boundary for the existing group structures. A connecting
arrow beta:P->susp C is constructed from the pushout property.
ConnectingArrow proves sigma(delta g) = Omega(beta_*)(L g), with an
explicit pointing for beta_*. The pointed loop map is a homomorphism;
transport along the same L and sigma gives the claimed additivity.
No new coherence or additivity parameters are introduced.

Boundary naturality is proved for a supplied coherent map of
representable pushout squares. Its input cube identifies the target
cone of postcomposition with the cone map induced by the two upper
faces. This is diagram-map data, not an extra ambient axiom. Both the
direct boundary and the structural positive-degree boundary are natural
under this hypothesis. BoundaryLoopComparison identifies the structural
boundary with the loop of the direct boundary. Constructing the cube
from maps of pushout diagrams of types remains open.

New files
---------
All                 alternate root and explicit input parameters
HigherCat           objects of an internal category
Constructions       edges and identity edges
Composition         composition and its triangle witness
SemiSegalBoundary3  the complete finite Lambda^3_1 matching telescope
Associativity       associator selected by horn3; characterizing equality
SemiSegalTetrahedra normalized tetrahedron family and its horn condition
SemiSegalNormalize  fibrewise normalization equivalences
SemiSegalBoundary4  the complete finite Lambda^4_1 matching telescope
SemiSegalPentagon   canonical 4-horn and the derived pentagon
CompLaws            unit laws from degeneracy triangles
InternalInverse     inverse fragment needed by dimension/Fubini/spheres;
                    exposed under the old module names for compatibility
HomologyUnits       group units are classes of categorical zero maps
HomologyMaps        homotopy/equivalence invariance and induced squares
MayerVietorisTail   exact pointed-set tail through degree zero
StableNaturality   suspension on arrows; naturality of the stable loop equivalence
PathFrames         endpoint changes for paths and the pointed-loop criterion
ConeCocone         interchange between cone and cocone evaluation from pentagon
ZeroPreCoherence   coherence of precomposition with zero under composition
ZeroCocone         evaluation of the meridian cocone after changing endpoints
ConnectingArrow   connecting arrow and comparison with the direct boundary
BoundaryAdditivity the existing direct boundary preserves existing multiplication
StableGroupMaps    postcomposition and degree-zero homology maps are additive
PointedBoundaryNaturality  pullback boundary naturality with actual pointings
PostSquare         pointed postcomposition squares from categorical squares
MayerVietorisNaturality  direct boundary naturality for representable cubes
BoundaryLoopComparison  structural boundary equals the looped direct boundary
BoundaryNaturality structural boundary naturality for representable cubes
MayerVietorisZeroGroups  additive boundary/inclusion/difference and exactness

All other .seg files are relative links, not copies.

Validation (2026-11-01)
-----------------------
changed and all pass: 114 modules, 0 failures.
Fresh --opened: 2876 declarations, 0 failures, 3.13 s.
Every module is under 1 s. Original hcat: changed reports nothing
changed; all passes, 169 modules, 0 failures. Hash comparison confirms
all 169 original .seg files are unchanged. Both servers stopped.
Mathematical note: ../../doc/hcat-segal-refactor.tex and its PDF.
Homology continuation: ../../doc/hcat-segal-homology.tex and its PDF.

Next mathematical steps
-----------------------
Continue homology: construct the representable cube from maps of type
pushouts. Independently, construct the
finite semi-Segal inputs in an intended model or from an ambient coherent
Cat presentation. Model construction is not a prerequisite for these
synthetic proofs. This root does not discharge hpent for the old
associator or complete the proposed ambient degree-5 proof.
The sibling hcat-spectrum root now assembles the existing K(M,n) into
checked coefficient Omega-spectrum data; it is not yet a model of D.
See HANDOFF.txt for the current theorem names and remaining proof targets.
