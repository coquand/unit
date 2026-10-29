# Universal properties for core/ (notes for later, 2026-10-29)

## Diagnosis

The informal text of core was too concrete: it exposed construction
details instead of universal properties, and was hard to follow.  The
abstraction attempt (core-abstraction step 1, stopped; see
HANDOFF-ABSTRACTION.md "Step 1: stopped") hid the representation without
replacing the argument: it turned `(x, a)`, `.1`, `.2` into `pr`, `pr1`,
`pr2` with explicit type and stage, so the concrete argument stayed and
the notation grew longer.

What was missing is the choice of which universal properties shorten the
downstream proofs, including their substitution laws.  For a
comprehension:

    Sub(Δ, Γ.A)  ≃  Σ (σ : Sub(Δ, Γ)) Term(Δ, A[σ])

Pairing builds the substitution, projection and generic term
characterise it, and uniqueness proves equalities.  The concrete
encoding should establish this interface once.  The scheme development
works better for the same reason: localisation, universal support,
limits and unique amalgams decide how later arguments go.  Uniqueness
does mathematical work there; it does not merely protect an
implementation.

## Two patterns seen during the migration

1. **A point of Γ.A is determined by its projection and its term.**
   Proved again by hand each time, with `idJ` on the first component,
   `apH` of the pairing, and a fibre-specific extensionality (`Dext`,
   `Kext`, `path-eq`):
   CId.tpI-ext, CCosk.EKext, CLocDCart.extG / extD, CLocComp.tdExt,
   CLocPath.DEext / DE2ext, CPostLimit.lext, and the tAinj / tBinj
   lemmas of CUaB, CUaD, CFibU1.  `TyL.pr-eqV` covers only the plain
   case; the variants differ by the equality of the fibre.

2. **Carts are pullback squares written out field by field.**
   `CCart.Cart` takes `s, s-nat, ta, tapt, tanat, tainj, bk, bkta`.
   Mathematically: a map Δ.A' → Γ.A over s that is a fibrewise iso, i.e.
   A' ≅ A[s].  This is where the notation cost most: the 51-argument
   telescope of CGlueCartNat, the ~600-character `PtA` parameter, the
   identity carts spelled out (`\ W v -> refl v.1, \ Y y u -> refl (y, u)`)
   in about 19 files.  From the universal property, identity and
   composite carts come for free; CCartLaws2 CC / CG and much of
   CHFibLaws HComp / HCong should follow by uniqueness.

## Caveat

Many current proofs use β and η of pairs by computation: `pr1 (pr x b)`
reduces to `x`, `tapt` of an identity cart is `refl`.  If the universal
property holds only up to a path, every use pays a transport (`subst`,
`coeT`) and coherence lemmas appear.  This is the usual way an abstract
rewrite becomes longer than the concrete one.  So let the universal
property carry uniqueness and comparison, and keep β by computation where
the encoding already gives it.

## Method

Choose one difficult argument, rewrite it informally through the relevant
universal properties, then formalise that version locally.  Migrate
further only if the experiment gives a clearer proof.  Measure as in
step 1 (segd --opened --only M, alternating runs).

Candidate: composition of carts (CCartLaws2) together with one user,
CGlueCartNat or CLocDNUniv.  It is small enough to rewrite informally in a
page.  Pattern 2 is its whole content, so if the universal property does
not shorten it, it will not shorten anything else.  It includes the 1.1 s
declaration CLocDNUniv.Nat.nat, which makes it a check on time as well as
on readability.
