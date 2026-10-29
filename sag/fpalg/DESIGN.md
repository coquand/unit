# sag/fpalg: finitely presented algebras as a small univalent category

The categorical packaging of sag/presentations with sag/categories.  No new
algebra representation, no new polynomial or quotient construction, no
shared file modified.  R is a commutative ring whose carrier is a set
(`setR`), fixed throughout (`Over[R,setR]`).

## 0. The objects and arrows (existing, sag/presentations/Algebras.seg)

An R-algebra A (`Algebras.Over[R,setR].Algebra`) is a commutative ring
`A.ring` (`Ring.CRing`), a proof `A.set` that its carrier is a set, and a
ring map `A.iota : R -> A.ring`.  An algebra map f : A -> B (`Hom A B`) is a
ring map f (a function f0 with f0 1 = 1, f0 (a + b) = f0 a + f0 b,
f0 (a b) = f0 a f0 b: `RingHom.Hom`) with f0 (iota_A r) = iota_B r for
every r (`Commutes`, a proposition).  `identity`, `compose`, and `ext`
(maps with pointwise equal carrier maps are equal) are given there.

Levels: Algebra : U (l+1) (it contains a type of U l), Hom A B : U l.

## 1. The precategory (AlgebraCategory)

* Hom A B is a set: ring maps into a set form a set (`RingHom.Properties.set`)
  and Commutes is a proposition.
* By definition the carrier map of `compose g f` is a |-> g0 (f0 a), and
  that of `identity A` is a |-> a (refl lemmas `compose-fun`,
  `identity-fun`).  So the unit and associativity laws hold pointwise by
  refl, hence by `ext`.

This gives `pre : Category[l+1, l].Precategory` with objects Algebra.

## 2. Isomorphisms and carrier equivalences (AlgebraCategory)

**Lemma 2.1 (inverse).**  Let f : Hom A B with f0 an equivalence; let g0 be
its section, so f0 (g0 b) = b (`sec-eq`) and g0 (f0 a) = a (`sec-ret`).
Then g0 underlies an algebra map g : B -> A:
* g0 1 = g0 (f0 1) = 1;
* g0 (b + b') = g0 (f0 (g0 b) + f0 (g0 b')) = g0 (f0 (g0 b + g0 b'))
  = g0 b + g0 b'  (sec-eq twice, f0 additive, sec-ret); the same for products;
* g0 (iota_B r) = g0 (f0 (iota_A r)) = iota_A r  (f commutes, sec-ret).
Moreover g o f = 1_A and f o g = 1_B, pointwise by sec-ret and sec-eq,
hence by `ext`.  So (f, g) is an isomorphism of the precategory whose arrow
is f.

**Lemma 2.2.**  If (f, g, g o f = 1, f o g = 1) is an isomorphism of the
precategory, f0 is an equivalence with inverse g0: evaluating the two
equations at a point (ap of evaluation) gives g0 (f0 a) = a and
f0 (g0 b) = b, through `compose-fun` and `identity-fun`.

## 3. The structure notion and the existing Hom (AlgebraSIP)

An algebra structure on a type X in the sense of sag/sip/SipGeneric:

* data: a point z, a point o, binary operations + and ., a unary operation
  -, and a map c : R -> X.  SipGeneric has `point` and `binop`; the two
  other pieces are local:
  - `unop`: S X = X -> X; e is a homomorphism s -> t when e (s x) = t (e x)
    for all x;
  - `from K`: S X = K -> X; e is a homomorphism s -> t when e (s k) = t k.
  For both, the structures t on X with the identity a homomorphism from s
  are the singleton of pointwise paths at s (`hsing`), which is
  contractible: the `unit` of the notion.
* axioms: X is a set, the eight CRing laws, and c preserves 1, + and .
  Given that X is a set each is a proposition (function extensionality);
  "X is a set" is itself a proposition.

`fields A` reads an Algebra as such a structure on A.ring.R, and `mk`
builds an Algebra from one.  By definition `mk (fields A)` is A once A and
A.ring are split into their constructors (record eta, used once in `back`).

**Correspondence of the homomorphism predicates.**  For an equivalence
e : A0 ~ B0 of carriers,
* Iota(e) (the notion's predicate) says: e preserves z, o, +, ., - and
  e (c_A r) = c_B r;
* the Hom structure on e0 (`RingHom.Preserves` and `Commutes`) says: e0
  preserves o, + and ., and e0 (iota_A r) = iota_B r.
From Iota to Hom: forget z and -  (`to-hom`).  From Hom to Iota: preservation
of z is `RingHom.zero` (f 0 = f (0 + 0) = f 0 + f 0, then cancel) and of -
is `RingHom.negation` (f (-a) is an additive inverse of f a, and inverses
are unique) (`to-iota`).  Both sides are propositions (B0 is a set), so
these two maps form a logical equivalence of propositions.

## 4. Univalence (AlgebraSIP)

By `Category.FromTotal` it suffices that Singl A = (B : Algebra) * Iso A B
is a proposition for every A.  SipGeneric proves that the total space
(B : Str) * Iso_N (fields A) B is contractible (`Over[N].total-contr`, by
induction on carrier equivalences and the units of the pieces).  Singl A is
a retract of it:

* s (B, i) = (fields B, (f0, Lemma 2.2), to-iota f), f the arrow of i;
* r (B', (e, t)) = (mk B', the iso of Lemma 2.1 for the map with carrier e0
  and structure to-hom t);
* r (s (B, i)) = (B, i): after record eta (split on B and B.ring) the first
  component is B by definition; the arrow of the rebuilt iso has carrier f0,
  so it equals the arrow of i by `ext` (pointwise refl), and an iso is
  determined by its arrow (`Arrows.iso-eq`).

A retract of a contractible type is a proposition.  So `category :
Category[l+1, l].Category`: **checkpoint 1**, the univalent category of
small commutative R-algebras.

## 5. The small full image of the presented algebras (FPImage)

Codes: `Presentations.Presentation` (n and a finite list of equations in n
variables), in U l.  Interpretation: F p = `PresentedAlgebra[l].Over[R,setR,p].algebra`
(the quotient of expressions; it satisfies the universal property
`PresentationExistence.presentation`).  `SmallImage[l+1, l].SmallFullImage`
gives:

* `category : Category[l,l].Category`, objects in U l (replacement at
  `Replacement[l, l+1]`, the Hom types being small by univalence of §4);
* a fully faithful inclusion into the algebras;
* **characterisation of the objects**: an algebra A lies in the image
  (the fibre of the inclusion over A, a proposition) iff
  || (p : Presentation) * Iso_R (F p, A) ||;
* (q p = q p) ~ Aut_R (F p): automorphisms are kept.

**Checkpoint 2.**

**Comparison with FP (FPComparison).**  For every algebra A,

  A lies in the image  ~  FP A,

an equivalence of propositions.
* FP A -> image.  Eliminate the truncation (the target is a proposition).
  A witness is p with Presents p A.  F p also has presentation p
  (`PresentationExistence.presentation`), so `PresentationComparison` gives
  algebra maps F p -> A -> F p that are inverse to each other, i.e. an iso
  F p ~ A.  Then (p, iso) is a generator, and A lies in the image.
* image -> FP A.  A lies in the image, so merely there is p with an iso
  i : F p ~ A.  By univalence of the category of algebras (§4), i gives a
  path F p = A, and transporting Presents p (F p) along it gives
  Presents p A.

So the objects of the small category are exactly the algebras that are
finitely presented in the sense of the universal-property predicate FP.

**Smallness.**  Ob(D_F) ~ (A : Algebra) * FP A, the left side in U l, the
right side in U (l+1).  A map with propositional fibres has domain
equivalent to the sum of its fibres; here the fibres are equivalent to FP A
by the comparison.  Directly: a |-> (i a, FP proof of (a, refl)); back,
(A, u) |-> first component of the fibre point of u.  The round trip from a
is the first component of a path in a proposition (the fibre over i a); the
round trip from (A, u) is (i a', _) with p : i a' = A, equal to (A, u)
along p because FP A is a proposition.  So the type of finitely presented
algebras has a small model, by replacement and without propositional
resizing.

## 6. Descent of functors on codes (FPDescent)

`CompletionUP[l+1, l, m, n, j].Instance` with the same D, codes and F:
C_F has the codes as objects and Hom_R (F a, F b) as arrows, q : C_F -> D_F
is fully faithful and essentially surjective, and for every category
E : Category[m,n], with l, m, n <= j,

  q^* : Fun(D_F, E) -> Fun(C_F, E),  G |-> G o q,

is an equivalence of types (`Universal[E].equiv`): a functor defined on
codes descends uniquely to the small category of finitely presented
algebras.

## 7. Set-valued functors and Yoneda (Yoneda, FPYoneda)

C is a small precategory (objects and arrows in U l); the instance is
C = D_F, the finitely presented algebras, whose arrows a -> b are
Hom_R (A_a, A_b).

**Set-valued functors.**  A covariant functor F : C -> Set is a family of
sets F x (in U l), maps F f : F x -> F y for f : x -> y, with F 1 u = u and
F (g o f) u = F g (F f u) pointwise.  A natural transformation
alpha : F -> G is a family alpha_x : F x -> G x with
alpha_y (F f u) = G f (alpha_x u).  Naturality is a proposition (G y is a
set), so transformations with pointwise equal components are equal
(nat-eq).  Nat (F, G) lies in U l because the objects are small.

**Representables.**  h_A x = C (A, x), with h_A f g = f o g; the laws are
the unit law 1 o g = g and associativity.  For the algebras,
h_A (B) = Hom_R (A, B): the affine scheme Spec A as a functor of points.

**Yoneda.**  For every F, evaluation at the identity,
eval alpha = alpha_A (1_A), is an equivalence Nat (h_A, F) ~ F A.  The
inverse sends u in F A to ext u, ext u_x f = F f u, which is natural:
ext u_y (f o g) = F (f o g) u = F f (F g u).
* eval (ext u) = F 1 u = u.
* ext (eval alpha) = alpha, componentwise:
  F f (alpha_A 1) = alpha_x (f o 1) = alpha_x f, by naturality of alpha at f
  applied to 1_A, and the unit law.

**Affine representables.**  With F = h_B: Nat (h_A, h_B) ~ C (B, A), and
the inverse is y f = ext f, with (y f)_x g = g o f: precomposition with f.
So y is a bijection on hom sets.  It reverses composition: y 1 = 1 (unit
law) and y (f o g) = y g o y f (associativity), so the representable
embedding is a fully faithful functor with source C^op; for the algebras,
(Alg_R^fp)^op.
