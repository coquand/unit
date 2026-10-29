# Univalent categories as structured 1-types (`sag/categories`)

Design: `doc/univalent-categories.tex`.  This file states the informal
mathematics each `.seg` file follows; every declaration is a step or a
lemma below.  Setting: the `Theory` segment of `All.seg` (univalence and
replacement, the parameters of `sag/replacement`); function extensionality
`fe` is derived from univalence in `Theory` as in `sag/replacement`, and is
used from §4 on (not in §1-3).  No other axiom.

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

`sag/replacement/Completion.seg` is not literally an instance of this
theorem.  It takes the image of a family `A -> U l` of arbitrary types,
with paths identified with equivalences; equivalences between arbitrary
types need not form sets, so `U l` with equivalences is not a category in
the sense of §1.  It is the same image argument at a more general homotopy
level.  Restricting to families of sets (`Set_l`, whose equivalences are
the isomorphisms of a category with hom sets the functions) gives a
categorical instance.  Neither proves the universal property of the
completion (§4).

## 4. The universal property of the completion

Files: `Arrows.seg` (arrows with hidden objects: laws, isos, cancellation,
`square-inv`), `Functor.seg` (`EssSurj`, `SplitEssSurj`, `Maps`: functors
preserve isos; `Faithful`: `pre`, `faithful`, `reflect-iso`, `lift`,
`unique`, `paste`), `FunctorCat.seg` (4.1), `PrecomposeFF.seg` (4.2),
`Descent.seg` (4.3), `UniversalProperty.seg` (4.4), `CompletionUP.seg`
(4.5); `completion.opens` records what each declaration opens.

After HoTT book §9.9 (Lemmas 9.9.1-9.9.2, Theorem 9.9.4), stated for an
arbitrary weak equivalence and then instantiated at `q : C_F -> D_F`.
Function extensionality (`fe`, derived from univalence in `Theory`) is
needed from here on: natural transformations are compared componentwise.

Notation.  `B`, `C` precategories, `E` a category, `q : C -> B` a functor
which is

- fully faithful: `q : C(c,c') -> B(qc,qc')` is an equivalence; then `q`
  reflects isomorphisms (the inverse of `q f` is `q` of the preimage, and
  the two identities hold after `q`, hence before);
- essentially surjective: for every `b`, `||(c : C) * Iso_B(qc, b)||`.

For an iso `e` write `e^-1` for its inverse.  "Merely pick (c, e)" means:
the goal is a proposition, so eliminate the truncation of essential
surjectivity into it.

### 4.1 Functor categories

`Nat(G,H)` for `G, H : B -> E`: `alpha : (b : B) -> E(Gb,Hb)` with
naturality `Hg o alpha_b = alpha_b' o Gg` for `g : B(b,b')`.  Naturality is
a proposition (hom sets), so `alpha = alpha'` iff `alpha_b = alpha'_b` for
all `b` (fe), and `Nat(G,H)` is a set.  Identity and vertical composite
are componentwise; the laws hold componentwise.  This is the precategory
`Fun(B,E)`.  Precomposition `q^* : Fun(B,E) -> Fun(C,E)` is
`G |-> G o q` and `(q^* alpha)_c = alpha_{qc}`; it is a functor by
definition (refl lemmas).

Universe bounds: `B, C : Precategory[k,l]`, `E : Category[m,n]` (at
`C_F`, `D_F` both `k` and `l` are `l`), and a level `j` with
`k, l, m, n <= j` (constraints); `Fun(B,E) : Precategory[j,j]`, and
function extensionality is used at `j`.  Its objects are in
`U (k \/ l \/ m \/ n)` and arrows in `U (k \/ l \/ n)`, which `j` bounds.

### 4.2 Lemma A (q^* is fully faithful)

For `G, H : B -> E`, `alpha |-> q^* alpha : Nat(G,H) -> Nat(Gq,Hq)` is an
equivalence.  `E` need only be a precategory here.

*Proof.*  Fix `beta : Nat(Gq,Hq)`.  For `b : B` let
  `T_b = (gamma : E(Gb,Hb)) * ((c : C) (u : B(qc,b)) ->
                                 gamma o G u = H u o beta_c)`,
the condition at every arrow `u`, not only at isos (this makes (iii)
need one chosen `(c, e)`).

(transfer) If `u' o q f = u` (`f : C(c,c')`) and the condition holds at
`(c', u')`, it holds at `(c, u)`:
  `gamma o G u = (gamma o G u') o G q f = H u' o beta_c' o G q f
              = H u' o H q f o beta_c = H u o beta_c`
(functoriality, naturality of `beta` at `f`).

(i) `T_b` is a proposition.  The second component is a proposition (hom
sets, fe), so it suffices that `gamma = gamma'` for two elements; this is a
proposition, so merely pick `(c, e)`.  Then `gamma o Ge = He o beta_c =
gamma' o Ge`, and `Ge` is an iso, so `gamma = gamma'`.

(ii) `T_b` is inhabited.  It is a proposition, so merely pick `(c0, e0)`.
Put `gamma0 = (H e0 o beta_c0) o G(e0^-1)`; then `gamma0 o G e0 =
H e0 o beta_c0`.  For `(c, u)`: by fullness `u = e0 o q f` with
`f = lift e0 u : C(c,c0)` (the preimage of `e0^-1 o u`); apply transfer.

Let `alpha_b` be the first component of the element of `T_b`; so
`alpha_b o Gu = Hu o beta_c` for all `(c, u)` (*).

(iii) `alpha` is natural.  For `g : B(b,b')` the equation is a proposition;
merely pick `(c, e)` for `b`.  By (*) at `b` and at `(c, g o e)` for `b'`,
  `(Hg o alpha_b) o Ge = Hg o He o beta_c = H(g o e) o beta_c
     = alpha_b' o G(g o e) = (alpha_b' o Gg) o Ge`,
and `Ge` is an iso.

(iv) `q^* alpha = beta`: (*) at `(c, 1_{qc})` gives `alpha_{qc} = beta_c`
(`G 1 = 1`, `H 1 = 1`).

(v) Uniqueness.  If `alpha'` is natural with `q^* alpha' = beta`, then
`(alpha'_b, -)` is in `T_b`: naturality of `alpha'` at `u` gives
`alpha'_b o Gu = Hu o alpha'_{qc} = Hu o beta_c`.  By (i)
`alpha'_b = alpha_b`, so `alpha' = alpha` (4.1).

So `beta |-> alpha` is inverse to `q^*` ((iv), (v)).  QED.

### 4.3 Lemma B (descent of functors)

For `G : C -> E` there are `H : B -> E` and a natural iso `H o q ~ G`.
Here `E` must be univalent.

*Objects.*  For `b : B` let
  `X_b = (x : E.ob) * (h : (c : C) -> Iso_B(qc,b) -> Iso_E(Gc,x)) *
         ((c c' : C) (f : C(c,c')) (e : Iso_B(qc,b)) (e' : Iso_B(qc',b)) ->
            e' o q f = e -> h c' e' o G f = h c e)`
(equations of underlying arrows).  `X_b` is contractible: being
contractible is a proposition, so merely pick `(c0, e0)`.  The map
  `X_b -> (x : E.ob) * Iso_E(Gc0, x)`,   `(x, h, k) |-> (x, h c0 e0)`
is an equivalence, and its codomain is contractible (univalence of `E`:
it is equivalent to the based path space `(x : E.ob) * (Gc0 = x)`).
Formally only the retraction is used: `X_b` is a retract of
`(x : E.ob) * Iso_E(Gc0, x)`, itself a retract of the based path space,
so `X_b` is a proposition (eliminating the truncation into the
proposition "`X_b` is a proposition"), and it is inhabited by the image
of `(G c0, 1)`.
Inverse: `(x, phi)` goes to `h c e = phi o G f` where `q f = e0^-1 o e`
(`f` is an iso as `q` reflects isos, so `h c e` is one); `k` holds since
`e' o q f = e` gives `q (f'_e' o f) = q f_e` hence `f_e' o f = f_e`
(faithfulness), and `h c' e' o G f = phi o G(f_e') o G f = phi o G f_e`.
The two composites are identities: one way `h c0 e0 = phi o G 1 = phi`;
the other way `k` at `f_e` (with `e0 o q f_e = e`) gives `h c e =
h c0 e0 o G f_e`, the remaining components being propositions.
Put `H b = x`, `eta_b = h` (the centre of `X_b`).

*Arrows.*  For `g : B(b,b')` let
  `Y_g = (phi : E(Hb, Hb')) *
         ((c c' : C) (f : C(c,c')) (e : Iso_B(qc,b)) (e' : Iso_B(qc',b')) ->
            e' o q f = g o e -> phi o eta_b c e = eta_b' c' e' o G f)`.
`Y_g` is contractible.  Proposition: two `phi` agree after the iso
`eta_b c e` for a merely chosen `(c, e)` together with `(c', e')` and the
`f` given by fullness.  Inhabited (a proposition, so merely pick `(c, e)`,
`(c', e')`): `phi = eta_b' c' e' o G f0 o (eta_b c e)^-1` with
`q f0 = e'^-1 o g o e`; for other data `(d, d', f, u, u')` with
`u' o q f = g o u`, write `u = e o q m`, `u' = e' o q m'` (fullness, `m`,
`m'` isos); then `q (m' o f) = q (f0 o m)` and by faithfulness
`m' o f = f0 o m`; by `k` of `X_b`, `X_b'`: `eta_b d u = eta_b c e o G m`
and `eta_b' d' u' = eta_b' c' e' o G m'`, which give the equation.
Put `H g = phi`.

*Functoriality.*  `1_{Hb}` satisfies the condition of `Y_{1_b}` (it is `k`
of `X_b`), and `H g' o H g` that of `Y_{g' o g}` (paste the two squares,
the middle `(c', e')` chosen merely); so `H 1 = 1`, `H (g' o g) = H g' o H g`
by contractibility.

*`H o q ~ G`.*  `eps_c = (eta_{qc} c 1)^-1 : Iso_E(H(qc), Gc)`.
Naturality at `f : C(c,c')` is the condition of `Y_{q f}` at
`(c, c', f, 1, 1)`: `H(q f) o eta c 1 = eta c' 1 o G f`.  QED.

### 4.4 Theorem (universal property of the completion)

For `q : C -> B` fully faithful and essentially surjective and `E` a
category, `q^* : Fun(B,E) -> Fun(C,E)` is fully faithful (Lemma A) and
split essentially surjective (Lemma B), i.e. an equivalence of categories.

*Corollary (equivalence of object types).*  If moreover `Fun(B,E)` and
`Fun(C,E)` are categories, `q^*` on objects is an equivalence of types.
Proof: let `P : X -> Y` be fully faithful and split essentially surjective,
`X`, `Y` categories.  By univalence of `Y` the fibre `(x : X) * (P x = y)`
is equivalent to `S_y = (x : X) * Iso_Y(Px, y)`, which is inhabited.  It is
a proposition: for `(x, e)`, `(x', e')` in `S_y`, a path is a pair
`(p : x = x')` with `e` transported along `p` equal to `e'`; by
univalence of `X`, `p = isotoid phi` with `phi : Iso_X(x,x')`, and the
transport of `e` is `e o (P phi)^-1` (J, then `idtoiso` of `isotoid`).  So
the paths form `(phi : Iso_X(x,x')) * (e' o P phi = e)`, which is
contractible: `P phi = e'^-1 o e` determines the arrow `phi` (ff), and it
is an iso as `P` reflects isos; the equation is a proposition.

*Univalence of functor categories* (doc Proposition 1.1), needed for the
corollary: for `E` a category and `F : B -> E`, the total space
`(G : Fun(B,E)) * Iso_Fun(F, G)` is contractible; this is the structure
identity principle (`sag/sip/SipGeneric`, Fundamental, can be linked
read-only).  It is equivalent to
  `(G0 : B.ob -> E.ob) * (a : (b : B) -> Iso_E(Fb, G0 b)) *
   (G1 : arrows) * (naturality of a) * (laws)`;
`(G0, a)` is contractible (fe, and univalence of `E` pointwise), and given
`(G0, a) = (F.obj, 1)` naturality says `G1 g = F g`, a singleton (fe); the
laws are propositions.  An iso of functors is a natural transformation
whose components are isos (inverse componentwise, natural automatically).

Implementation note: records have no definitional eta, so paths between
functors pass through the eta lemma of the record (`split`), or functors
are compared through the Sigma form above.

### 4.5 Instance

`C_F`: objects `A`, arrows `C_F(a,b) = D(Fa,Fb)`, the rest from `D`.
`q : C_F -> D_F` is `image.quotient` on objects and conjugation on arrows,
`q h = t_b^-1 o h o t_a` with `t_a = idtoiso_D (triangle a) : Iso_D(i q a, F a)`;
it preserves identities and composites (`t t^-1 = 1`); it is fully
faithful (conjugation by isos has the inverse `h' |-> t_b o h' o t_a^-1`);
it is essentially surjective by `generated` (§3.1), composing with `t`.
Hence `q^* : Fun(D_F,E) ~ Fun(C_F,E)` for every category `E` (4.4), and,
`D_F` being a category, the corollary applies.

Order of work: 4.1, Lemma A, Lemma B, Theorem 4.4, instance 4.5 (done,
checked); then univalence of functor categories and the corollary (not
done).
