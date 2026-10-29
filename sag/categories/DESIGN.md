# Univalent categories as structured 1-types (`sag/categories`)

Design: `doc/univalent-categories.tex`.  This file states the informal
mathematics each `.seg` file follows; every declaration is a step or a
lemma below.  Setting: the `Theory` segment of `All.seg` (univalence and
replacement, the parameters of `sag/replacement`); function extensionality
is not used in the first milestone.  No other axiom.

Universe bounds.  A category `C : Category[k,l]` has objects in `U k`
and arrows in `U l`; "small" means in `U l`.  Nothing forces `l <= k`
or `k <= l`; for the categories of interest (algebras with small
carriers) `k = l+`.

## 1. Categories (`Category.seg`, levels k l)

**Precategory.**  A type `ob : U k`; sets `hom x y : U l`; `idn x`;
`comp x y z g f : hom x z` for `g : hom y z`, `f : hom x y`; the laws
`idn o f = f`, `f o idn = f`, `h o (g o f) = (h o g) o f`.  No condition
on `ob`.

**Isomorphisms.**  `isIso f` for `f : hom x y` is
`(g : hom y x) * (g o f = idn x) * (f o g = idn y)` and
`Iso x y = (f : hom x y) * isIso f`, in `U l`.  `Iso x y` is a set: a
Sigma of the set `hom x y` and of sets (`hom y x` with two identity types
of sets, which are propositions, hence sets).  The identity iso is
`iso-id x = (idn x, idn x, l, l)` with `l = idn o idn = idn` (left unit).

**idtoiso.**  `idtoiso x y : (x = y) -> Iso x y` is J with value
`iso-id x` at `refl x`; this is a refl lemma (`idtoiso-refl`).

**Category.**  A precategory with `univalent x y : isEquiv (idtoiso x y)`
(at `U (k \/ l)`).  We write `isotoid` for its section.

Lemma (locally small).  `x = y` is small: the pair
`(Iso x y, isotoid)` with `isotoid` an equivalence (section of an
equivalence, inverse by `sec-eq` and `sec-ret`).  This is
`Replacement[l,k].LocallySmall ob`, the hypothesis replacement needs.

Lemma (1-type).  `x = y` is a set: it is a retract of the set `Iso x y`
(`s = idtoiso`, `r = isotoid`, `r s = id` by `sec-ret`).
So the object type of a category is a 1-type; univalence is a structure
on the 1-type, the canonical map being the equivalence.

## 2. Functors (`Functor.seg`, levels k1 l1 k2 l2)

A functor `F : C -> D` of precategories: `obj : C.ob -> D.ob`,
`map x y : C.hom x y -> D.hom (obj x) (obj y)` preserving identities
and composites.  `F` is fully faithful when every `map x y` is an
equivalence (at `U (l1 \/ l2)`).

## 3. Small full image (`SmallImage.seg`, levels k l)

**Theorem (small full image).**  Let `D : Category[k,l]` and
`F : A -> D.ob` with `A : U l`.  There are a category
`D_F : Category[l,l]` (small objects, small arrows) and a fully
faithful functor `i : D_F -> D` such that

1. every object `a` of `D_F` satisfies `||(p : A) * Iso (F p) (i a)||`;
2. for `x : D.ob`, the fibre `(a : D_F.ob) * (i a = x)` is a proposition,
   and it holds iff `||(p : A) * Iso (F p) x||` (the essential image of
   `i` is the closure of the family under isomorphism, without choice
   of representatives);
3. `D_F.ob` is a 1-type, and for `p p' : A`,
   `(q p = q p') ~ Iso (F p) (F p')`; in particular
   `(q p = q p) ~ Aut (F p)`: the automorphisms are retained.

*Proof.*  `D.ob` is locally small (§1).  Replacement gives
`A --q--> I --i--> D.ob` with `I : U l`, `i (q p) = F p` (triangle) and
`ap i : (a = b) -> (i a = i b)` an equivalence (embedding); `q` is
surjective onto propositions of every size.

*Definition of D_F.*  Objects `I`; `D_F(a,b) = D(i a, i b)`; identities,
composition, the set condition and the laws are those of `D` at
`i a, i b, ..`.  By definition `Iso_{D_F}(a,b) = Iso_D(i a, i b)` and the
inclusion `i` (identity on arrows) is a functor; it is fully faithful as
`map a b` is the identity.

*Univalence.*  Lemma (`idtoiso-ap`): `idtoiso_{D_F} a b p =
idtoiso_D (i a) (i b) (ap i p)`, by J on `p` (both are `iso-id (i a)` at
`refl`).  The right side is the composite of the equivalences `ap i`
(embedding) and `idtoiso_D` (univalence of `D`), so `idtoiso_{D_F}`,
pointwise equal to it, is an equivalence.  Hence `D_F` is a category, and
its object type is a 1-type by §1.

*1.*  `a |-> ||(p : A) * Iso (F p) (i a)||` is a family of propositions on
`I`; by surjectivity of `q` it suffices to inhabit it at `q p`, by
`(p, idtoiso (F p) (i (q p)) (triangle p)^-1)`.

*2, fibres are propositions.*  First at `x = i b`: for `u : i a = i b`,
`u = ap i (sec u)` (`sec-eq`), and `(a, ap i r) = (b, refl)` for every
`r : a = b` by J on `r`.  For general `x` and `(b, v)` in the fibre,
J on `v` reduces to `x = i b`, `v = refl`, so every element equals
`(b, v)`.
*2, the equivalence.*  From the fibre: transport 1. along `v : i a = x`.
To the fibre: the fibre is a proposition, so eliminate the truncation;
from `(p, e)` take `(q p, triangle p . isotoid e)`.

*3.*  `(q p = q p') ~ (i (q p) = i (q p'))` (embedding)
`~ (F p = F p')` (conjugation by the triangles: J on both paths, the
identity at refl) `~ Iso (F p) (F p')` (univalence of `D`).  QED.

The construction chooses no representatives: `I` is not the set of
isomorphism classes, whose loops would be trivial.

What `sag/replacement/Completion.seg` proves is the case `D = U l` with
equivalences (the univalent completion of a family of types); it is the
template of the argument above, not the categorical universal property
(Rezk completion, `doc/univalent-categories.tex` Theorem 3.1), which is
NOT proved here.
