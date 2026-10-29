Univalent categories as structured 1-types (sag/categories)
===========================================================

Check:   ./segc sag/categories all

Design: doc/univalent-categories.tex; the informal proofs are in DESIGN.md
and at the head of each file.  Same Theory segment as sag/replacement
(univalence, images, surjections); no other axiom; function extensionality
(fe) is derived from univalence in Theory, as in sag/replacement, and used
from DESIGN.md §4 on.  Base, Prelude, Paths, Axioms, FunExtUA link to core;
Replacement, Truncation, TruncationCombinators link to sag/replacement.
Nothing outside this directory is modified.

  Equivalences   inverse, compose, homotopy, then, conjugate, lower
  Category       Precategory (Iso, idtoiso), Univalent, Category (isotoid),
                 Objects: locally-small (replacement's hypothesis), one-type
  Arrows         arrows with hidden objects: laws, isos, cancellation
  Functor        Functor, FullyFaithful, EssSurj, SplitEssSurj; Maps (isos
                 to isos), Faithful (pre, reflect-iso, lift, unique, paste)
  FunctorCat     NatTrans, FunCat (Fun(B,E)), Precompose (q^*)
  PrecomposeFF   LemmaA: q^* fully faithful
  Descent        LemmaB: descent of functors along q
  UniversalProperty  Theorem: q^* fully faithful + split ess. surjective
  SmallImage     SmallFullImage[D, A, F]: the small full image theorem
  CompletionUP   Instance: q : C_F -> D_F, and the theorem for every E

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

Completion.seg in sag/replacement is the same image argument for a family
of arbitrary types (paths ~ equivalences, which need not form sets), so it
is not literally the case D = U l of the theorem; restricted to families of
sets it is a categorical instance.

Theorem (CompletionUP.Instance.Universal, DESIGN.md §4).  With C_F
(objects A, arrows D(Fa,Fb)) and q : C_F -> D_F (quotient on objects,
conjugation by t_a = idtoiso (triangle a) on arrows), q is fully faithful
and essentially surjective, and for every category E : Category[m,n],
q^* : Fun(D_F,E) -> Fun(C_F,E) is fully faithful and split essentially
surjective.  The functor categories are Precategory[j,j] for a level j
bounding the others (constraints k l m n <= j).  completion.opens records
what each declaration of §4 opens (seg All.seg --opens completion.opens).

Not done here: univalence of functor categories and the corollary
(q^* an equivalence of object types), DESIGN.md §4.4.
