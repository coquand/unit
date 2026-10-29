Finitely presented R-algebras as a small univalent category (sag/fpalg)
=====================================================================

Check:   ./segc sag/fpalg all

The categorical packaging of sag/presentations with sag/categories; the
informal proofs are in DESIGN.md and at the head of each file.  Every
dependency is linked unchanged (core, sag/replacement, sag/categories,
sag/sip/SipGeneric, sag/polynomial, sag/projective/Quotient,
sag/presentations); Equivalences is sag/categories'.  Theory as in
sag/presentations: univalence and the two parts of replacement, fe and
propUA derived from univalence; no new axioms.

  AlgebraCategory  Over[R,setR]: pre : Category[l+,l].Precategory (objects
                   Algebras.Algebra, arrows Algebras.Hom); Inverse (Lemma
                   2.1: a map with an equivalence as carrier is an iso);
                   carrier-equiv (Lemma 2.2)
  AlgebraSIP       the notion of algebra structure (SipGeneric pieces point,
                   binop; local pieces unop, map-from R); fields/mk;
                   Iota vs Structure (iota-to-structure, structure-to-iota,
                   structure-prop: RingHom.zero, RingHom.negation);
                   At[A].singl-prop; univalent; category : Category[l+,l]
  FPImage          interpret p = PresentedAlgebra[l].Over[R,setR,p].algebra;
                   SFI = SmallImage[l+,l].SmallFullImage[category, codes,
                   interpret]; characterisation; automorphisms
  FPDescent        CU = CompletionUP[l+,l,m,n,j].Instance[category, codes,
                   interpret]; descent E

Checkpoint 1 (AlgebraSIP.Over.category).  Small commutative R-algebras
(carriers in U l) form a univalent category, Category[l+1, l]: objects in
U (l+1), arrows in U l.

Checkpoint 2 (FPImage.Over.SFI).  SFI.category : Category[l,l].Category,
objects SFI.image.carrier : U l, with the fully faithful SFI.inclusion into
the algebras, and
  characterisation A :  A in the image  <->  || (p : Presentation) * Iso_R (interpret p, A) ||
(the fibre of the inclusion over A, a proposition in U (l+1));
  automorphisms p : (q p = q p) ~ Aut_R (interpret p).

Descent (FPDescent.Over.descent E).  For every E : Category[m,n].Category,
with constraints l <= j, m <= j, n <= j,
  isEquiv Fun(D_F,E) Fun(C_F,E) (G |-> G o q)      (in U j)
where C_F has the presentations as objects and Hom_R(interpret a,
interpret b) as arrows, and D_F = SFI.category.  A functor on codes
descends uniquely to the finitely presented algebras.

Module-system note (integration only, not part of the mathematics).  The
checker forbids shadowing and has no renaming on import, and module names
are global, so independently written developments can collide:
 - PresentedAlgebra and PresentationExistence have local modules named
   Descent; All.seg imports them before sag/categories' file Descent.
 - sag/categories' CompletionUP had a nested module Universal, the name of
   sag/polynomial's file Universal; it is now CompletionUP.Instance.ForEvery.
 - sag/presentations and sag/categories each have a file Equivalences with
   different contents; this directory uses sag/categories'.

Open: "A in the image" vs Presentations.FP A (needs PresentationComparison,
which uses sag/presentations' Equivalences; see DESIGN.md §5).
