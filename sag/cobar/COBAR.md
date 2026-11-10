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
