# Towards π₄(S³) = ℤ/2 by delooping and a universal property

28 October 2026. Proposal of Thierry Coquand, developed from the discussion
of the Postnikov proof of π₃(S²) = ℤ. This is a research and formalisation
plan, not a completed proof. In particular, the criterion for belonging to
the image of looping remains to be proved in the required foundations.

## 1. The two categories and looping

Let C be the category of pointed, 1-connected, 3-truncated types, and D
the category of pointed, 2-connected, 4-truncated types. Write Map_* for
the type of pointed maps and [X,Y]_* for its set truncation.

Looping sends D to C and is fully faithful:

    Map_*(X,Y) ≃ Map_*(ΩX,ΩY),       X,Y in D.

This is the case n = 2 of David Wärn's Corollary 11: X n-connected and Y
2n-truncated suffice. It consequently gives full faithfulness on homotopy
classes, and, using univalence and reflection of equivalences, the claimed
embedding on the types of objects. These are distinct formulations and
should have explicit bridges in a formal proof.

The unique-delooping theorem for maps is already available as
`DeloopMaps.Maps.Over.cor11` in
[DeloopMaps.seg](../sag/em/DeloopMaps.seg). For a 1-connected 3-type,
Wärn's Corollary 8 also gives uniqueness of a connected delooping when
one exists; see `Deloop.Torsors.cor8` in
[Deloop.seg](../sag/em/Deloop.seg).

Let L denote the full subcategory of C consisting of types that merely
admit a delooping in D. Do not assume that every object of C lies in L.
Identifying L is the new mathematical task.

## 2. Transporting the universal property of the sphere

Suppose S³ is available with its sphere universal property, and put
T₃ = ‖S³‖₄. Establish that T₃ belongs to D. For Y in D, naturally in Y,

    [ΩT₃,ΩY]_* ≅ [T₃,Y]_* ≅ [S³,Y]_* ≅ π₃(Y) ≅ π₂(ΩY).

Thus ΩT₃ represents the underlying-set functor π₂ on L. It is a pointed
3-type equipped with a distinguished element of π₂, with the corresponding
universal property; it is not an unmarked initial object.

Compare this with T₂ = ‖S²‖₃, which represents π₂ on all of C. The desired
object is the universal replacement of this marked object within L.
An explicit equivalence on hom-sets, compatible with the marked element,
is needed. Object classification alone does not prove this assertion.

The final homotopy-group calculation would be

    π₄(S³) ≅ π₄(T₃) ≅ π₃(ΩT₃) ≅ ℤ/2,

as groups. Preservation of π₄ by truncation and the loop/group comparison
must be proved, rather than inferred from a bijection of underlying sets.

## 3. Why ℤ/2 should appear

The Postnikov description of C uses triples

    (A, B, k : K(A,2) →_* K(B,4)).

An additional comparison with quadratic maps describes k by a quadratic
map q : A → B, with q(−a) = q(a) and bilinear polarization

    b_q(a,a′) = q(a+a′) − q(a) − q(a′).

This quadratic comparison is not yet part of the checked Unit development.
In particular it must not be silently substituted for the actual mapping
theorem for Postnikov triples.

The expected description of T₂ is

    A = ℤ,   B = ℤ,   q(n) = n².

A candidate delooping criterion is that q be additive, equivalently that
its polarization vanish. For the rank-one case q(n) = n²b, computation gives

    b_q(m,n) = 2mn b.

Vanishing is therefore equivalent to 2b = 0. The universal abelian group
with a specified element b satisfying 2b = 0 is ℤ/2. This suggests the
candidate R in C with data

    A = ℤ,   B = ℤ/2,   q(n) = n² mod 2 = n mod 2.

The value q(1) is the nonzero generator. The polarization is zero, but q
itself is not zero. Confusing these would replace the intended Postnikov
extension by a split one and destroy the argument.

## 4. A formulation directly with the k-invariant

If κ : K(ℤ,2) →_* K(ℤ,4) is constructed and normalized as the cup square
in the π₃(S²) programme, form

    κ̄ = K(reduction mod 2,4) ∘ κ,
    R = Fib(κ̄).

The existing `PostnikovRealization.Triple` proves that this R is a simply
connected 3-type and that π₃(R) ≅ ℤ/2 once the coefficient group and map
are provided. A comparison with the quadratic invariant is still needed
to identify its q with n ↦ n² mod 2.

The anticipated multiplicativity condition on k is primitivity:

    k ∘ μ ≃ k ∘ pr₁ + k ∘ pr₂,

where μ is addition on K(A,2). For a cup square with coefficient b, the
cross term is 2b·(u₁ cup u₂). Modulo 2 it vanishes. This is a concrete
route to investigate, but an equality of cohomology classes by itself is
not a constructed delooping.

One must produce a suitably pointed homotopy, derive a unital multiplication
or a torsor structure on R, and invoke the precise delooping theorem.
Wärn's Corollary 8 is relevant here: in this dimension, a torsor inhabitant
is enough to construct the connected delooping. The required unit
coherences must be supplied explicitly; do not assume associativity or an
infinite coherence structure without proof.

For the universal property, prove that for any X in L, maps R →_* X on
homotopy classes are classified by an element a of π₂(X). In quadratic
language, the map on π₃ must send the generator of ℤ/2 to q_X(a);
additivity and q_X(−a) = q_X(a) imply 2q_X(a) = 0. Existence and uniqueness
of the corresponding homotopy class still require the mapping theorem,
including its homotopy-ambiguity calculation.

It is enough to establish the cases needed for the two-map Yoneda argument
(targets R and ΩT₃). A full classification of L for arbitrary A and B is
not mandatory if a narrower proof supplies these cases.

## 5. Exact remaining obligations

1. Finish the π₃(S²) programme, retaining coefficient naturality and the
   normalization of κ. Its present conditional assembly is not this input.
2. Instantiate full faithfulness of looping in the (2-connected, 4-type)
   range; prove the consequences for pointed equivalences and hom-sets.
3. Prove the required delooping criterion. Separate necessity of zero
   polarization from sufficiency, and state precisely the coherences used.
4. Construct R and a delooping BR in D. Prove the marked universal property
   of R on L, at least for the two targets used in Yoneda.
5. Supply S³ with its universal property and compare BR with ‖S³‖₄. The
   current authorization of an S² axiom does not already supply an S³
   axiom or arbitrary suspensions. A construction, or a separately explicit
   sphere assumption for this future theorem, is required.
6. Apply π₃ to the comparison of loop spaces and obtain the group isomorphism
   π₄(S³) ≅ ℤ/2. No representatives of homotopy classes should be chosen.

Finite truncations themselves have now been constructed in
[Truncations.seg](../sag/pi3-s2-postnikov/Truncations.seg), with connected
units and dependent elimination into truncated families; see
[finite-truncation.tex](finite-truncation.tex). The existing π₃ comparison
can guide the π₄ version, but that version is not yet checked.

Follow all six rules in [WRITING.md](../../seg/WRITING.md): informal proof
before code, one name per notion, characterising lemmas and locks, explicit
intermediate points, named accessors, and per-declaration `--opened` /
`--opens` audits derived from the proof text. Do not modify the checker or
add axioms to make an open mathematical obligation disappear.

## 6. Reference and status

David Wärn, *Eilenberg–MacLane spaces and stabilisation in homotopy type
theory*, especially Corollaries 8 and 11:
[published article](https://doi.org/10.1007/s40062-023-00330-5).

The full-faithfulness range is established mathematics, with its general
map-delooping theorem already implemented in Unit. The calculation
2mn b and the universal property of the group ℤ/2 are elementary algebra.
The identification of the essential image in the required Postnikov
presentation, its coherent realization, and the resulting universal-object
comparison are the proposed next proof, not results certified by this note.
