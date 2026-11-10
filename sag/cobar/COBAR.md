# The cobar construction D on the cubical base (jonas.pdf §4)

Goal (DUALITY.md §6, item 2): check Lemma 11, Lemma 12, Lemma 14 and
Prop 13 for a concrete D, in sag-model's external (strict) style.

## Split

- canonicity-45: the presheaf layer PSh(C) over the base for C a V-small
  category, U, R, E = RU, and Lemmas 8 and 9 (representation choice in its
  design note).
- canonicity-4e: the weights P_n, D (Definition 10), Lemma 11, Lemma 12,
  then Lemma 14 and Prop 13.

## D in explicit form (the paper's notation after Definition 10)

For x : C0, an element of (DΓ)_x is a family

    u_{f0,...,fn}(i) : Γ_{x_n}

indexed by n ≥ 0, a chain of composable maps f0 : x0 -> x, ...,
fn : x_n -> x_{n-1} of C, and i : P_n, subject to (eq. (1)), for k < n:

    u_{f0,...,fk,f(k+1),...,fn}(∂_k i) = u_{f0,...,fk f(k+1),...,fn}(i)
    u_{f0,...,f(n-1),fn}(∂_n i)       = u_{f0,...,f(n-1)}(i) . fn

and (DA)_γ likewise, with u_{f..}(i) : A_{x_n}(γ_{f..}(i)). The unit is
τ(γ)_{f0..fn}(i) = γ . (f0 ... fn). This form never iterates E: D is
defined from C's chains directly, and E, R appear only in proofs.

## Weights

P_n ⊆ I^{n+1}: sequences with at least one coordinate equal to 1, i.e.
the union over k of [i_k = 1] (a cofibration of I^{n+1}: bigU of pre of
ptS e1 along the coordinates). ∂_k : P_{n-1} -> P_n inserts 0 at k.
Cosemisimplicial identities ∂_l ∂_k = ∂_k ∂_(l-1) for k < l.

## Lemma 12 in this form

Given a levelwise trivial fibrancy structure α on A (at every x : C0),
extend a partial element u of (DA)_x γ on φ by induction on the truncation
level m: at level m+1 and chain f0..f(m+1), the value u_{f..}(i) is fixed
on [i_k = 0] for each k (by (1), from level m) and on φ; glue these sides
(CPartial.Join over φ ∨ ⋁_k [i_k = 0]) and extend with α at x_(m+1). The
compatibility of the sides on overlaps is the cosemisimplicial identity.
Uniformity (commuting with restriction) holds because α does.

## Coding plan for D (canonicity-4e, 2026-11-10)

canonicity-45's layer (approved): option (b), C-indexed families of base
presheaves (CCtx: ob x : PCtx, act f : PSub), CTy likewise, LFib/LTriv
levelwise (pure reuse of Lines.Fib / ContrOp at each x), UTriv/CUnif
uniform in C via mapside; C at level a.

D_x from existing presheaf formers (Psh: Sigma, extensional Id, Pi), so
that naturality in the base direction is free:

    (DΓ)_x = Σ (u : Π_{n : N} Π_{ch : Ch_n(x)} Π_{i : P_n} Γ_{last ch})
               . (face equations (1) as Id types)

with N and Ch_n(x) (chains of length n+1 ending at x) constant presheaves
(V-codes: natV, SigV over C's obV/homV), and P_n a base presheaf: at stage
J, i : Fin(n+1) -> Hom J Iv with Lands J J (bigU J (n+1) (k |-> pre J Iv
(i k) (ptS e1))) (idH J); Lands is a proposition, so its proofs code by a
fixed code. Faces ∂_k: insert ptH J e0 at k; membership by bigU-in after
bigU-out.

## Representation of D (canonicity-45, Cobar.seg, in progress)

Chains have the last object as an index: Ch n x z (Chains.seg), with
comp n k (k <= n), drop n (top face, returns (z', c', last map)), rx
(C-action), and the semisimplicial identities. An element of (DΓ)_x at
base stage X is t with t n z c J g i : (Γ.ob z).ob J for c : Ch n x z,
g : J -> X, i : Pn n J; natural in J; inner faces
t (n+1) z c J g (d_k i) = t n z (comp n k c) J g i; top face
t (n+1) z c J g (d_(n+1) i) = Γ.act fm (t n z' c' J g i).

## Lemma 12 (trivial fibrancy), detailed proof for the formalisation

Input: α z : ContrOp (Γ.ob z) (A.ty z) for every z (levelwise; LTriv).
Output: UTriv (DΓ) (DA).

Fix x, a base stage X, γ in (DΓ)_x(X) and a side s of DA over γ: a
cofibration Q on X and partial values s_h for h : W -> X landing in Q
(each an element of (DA)_x(W, γ.h), natural in W). We build
u : (DA)_x(X, γ), i.e. u n z c J g i in A_z(J, γ n z c J g i), level by
level.

Level n, at (z, c, J, g, i). Solve one extension problem for α z at
stage J over γ n z c J g i, with cofibration

    Q_{n,g,i} = pre g Q  ∨  ⋁_{k <= n} [i_k = 0]      (a bigU on J)

and partial element given by
  - on pre g Q (h : W -> J landing): (s_{g h}) n z c W (id) (res h i);
  - on [i_k = 0] (h landing, so i.h = d_k i' for a unique i' : Pn (n-1) W):
      for k < n: u (n-1) z (comp (n-1) k c) W (g h) i'   (level n-1),
      for k = n: A.act fm (u (n-1) z' c' W (g h) i')     (drop).
Set u n z c J g i := (α z).kop J (γ n z c J g i) (that side).

Compatibility of the pieces (needed for Join):
  - [i_k = 0] ∧ [i_l = 0], k < l: by the faces of u at level n-1 and the
    semisimplicial identities (comp-comp, comp-drop, drop-drop) and the
    weight identity d_l d_k = d_k d_(l-1);
  - pre g Q ∧ [i_k = 0]: s is itself an element of DA, so it satisfies
    the faces.
Naturality in J: α's uniformity (kunif) and the naturality of the side's
pieces. Faces at level n: at a weight d_k i' the face [i_k = 0] is total,
so the extension equals the side there (rc-ext / the extension law of
ContrOp). Extension of s: on pre Q the side is s, hence u extends s.
Uniformity in C (CUnif): the construction at (x', rx g c) is literally
the one at (x, c) (u is defined by recursion on n, uniformly in c), so
the C-action commutes strictly, as in Lemma 9.

Formal shape: a record Up m of the levels n <= m with naturality, faces
and extension of s; step : Up m -> Up (m+1) extending; u n := the level n
of the m-th stage for m >= n (levels are never changed once built).
