Univalent categories as structured 1-types (sag/categories)
===========================================================

Check:   ./segc sag/categories all

Design: doc/univalent-categories.tex; the informal proofs are in DESIGN.md
and at the head of each file.  Same Theory segment as sag/replacement
(univalence, images, surjections); no other axiom; function extensionality
is not used.  Base, Prelude, Paths, Axioms, FunExtUA link to core;
Replacement, Truncation, TruncationCombinators link to sag/replacement.
Nothing outside this directory is modified.

  Equivalences   inverse, compose, homotopy, then, conjugate, lower
  Category       Precategory (Iso, idtoiso), Univalent, Category (isotoid),
                 Objects: locally-small (replacement's hypothesis), one-type
  Functor        Functor, FullyFaithful
  SmallImage     SmallFullImage[D, A, F]: the small full image theorem

Theorem (SmallImage.SmallFullImage).  D : Category[k,l] (objects in U k,
arrows in U l), A : U l, F : A -> D.pre.ob.  Then
  category        : Category[l,l]   objects image.carrier : U l
  inclusion       : Functor[pre, D.pre], fully-faithful
  one-type        : the object type is a 1-type
  generated       : every object is merely iso to some F p
  fibre-prop      : the fibres of inclusion are propositions
  from-fibre, to-fibre : x is in the image iff merely iso to some F p
  generator-paths : (q p = q p') ~ Iso (F p) (F p')
  automorphisms   : (q p = q p) ~ Aut (F p)
Replacement is used once, at Replacement[l,k] (images @l @k), with
surjectivity at @l (generated); the truncation is Truncation[l],
eliminated at level k \/ l (to-fibre).

smallimage.opens records, per declaration, the definitions the text
opens (seg All.seg --opens smallimage.opens: nothing else opened).

Not done here: the universal property of the completion (Rezk completion,
doc/univalent-categories.tex Theorem 3.1); Completion.seg in
sag/replacement is the case D = U l, not that universal property.
