# M0: the semantic interface

## 1. The endpoint, exactly

Inside the Theory segment of `sag/affine/All.seg`

    module Theory
     (univ        : [l] Axioms[l].Univalence)
     (images      : [l] [k] Replacement[l,k].Images)
     (surjections : [l] [k] [j] (Replacement[l,k].Surjectivity (images @l @k)) @j)

the target is the record type

    SAGAxioms[l,k].Over[R,setR].Assumptions   -- fields loc, sqc, zchoice

Scope (ruling 2026-11-09): only M1-M4 are formalised; the step from P to
Z is ~/COLL/SAG.pdf, accepted as correct.

The first endpoint (M0-M5) is: a model Z in which
1. the three Theory parameters are interpreted by terms of Z;
2. R is the generic ring G (with its set-ness), and the coefficient map
   k -> G is interpreted;
3. `Assumptions` has a term in Z, for all levels l, k (with G : U l by
   cumulativity), stable under substitution (a term in every context, not
   only a global point).

Only the *statement* has to be interpreted syntactically. The proofs of
loc, sqc and zchoice are semantic (M4, M5). `fe` and `propUA` are derived
in Unit from `univ`, so they need no separate field.

## 2. Audit: what the statement uses

The closure of the statement (types *and* the terms occurring in them)
consists of the following declarations.

| File (sag/affine) | Declarations |
|---|---|
| Prelude (presentations/) | isProp, isSet, IsEquiv (record), isEquiv, Equiv, idEquiv, ap, trans, sym |
| Ring | Top, Empty, Nat, Plus, List (data); Not; CRing (record); RL.unit; sym, trans, ap, subst; RL.add-cancel (via RingHom.zero) |
| RingHom | Preserves, Hom, identity, zero |
| Algebras | Algebra (record), base, Commutes, Hom, Spec, evaluation |
| Presentations | Fin, cong2, Expr (data), eval, natural, Equations, Zeros, zeros-natural, Presentation, Solutions, canonical, Presents, Witness, FP, SQC |
| FiniteIdeal | Sums.sum, Sums.lin |
| StandardOpens | Locality |
| Replacement | Small, LocallySmall, Embedding, Image (record), Images |
| Truncation | top-small, Trunc.image, Trunc.carrier |
| SAGAxioms | Loc, SQC, UnimodularWitness, Unimodular, ChoiceData, ZChoice, Assumptions |

Terms such as `canonical` contain proofs (`zeros-natural`, `natural`,
`RingHom.zero`). Their type-correctness relies on judgmental computation,
so the model must validate that computation strictly (Section 3).

Universe levels used: l (ring, algebras), l+ (FP, SQC, Presents, Witness),
k (Z-choice families), l \/ k, l+ \/ k+. Replacement is used in the
statement at `images @m @m` for m in {l, k, l \/ k, l+} (truncations),
always with codomain Top. The full schema (all levels, all codomains, and
`surjections`) is needed only to discharge the Theory parameters.

Not used by the statement: Path types, Glue, interval, HITs, choice,
excluded middle, decidable equality on any carrier.

## 3. The source fragment F_SAG and its strictness

Judgmental equality of Unit must become *strict (external) equality* in
the model. Internal paths are not enough (plan, M0). The rules below are
the ones that the statement's type-checking uses (checker, `src/Seg.hs`).

1. **Π-types** with β and η (the checker has function η).
2. **Σ-types and records**: pairs, projections, β. Records have *no* η
   in Unit, which is a weaker requirement on the model.
3. **Identity types** `Id A a b`, `refl`, `idJ` with **strict β** (`idJ` on
   `refl` reduces). In a cubical model this is Swan's identity type, not
   the path type.
4. **Inductive types** with dependent elimination (`split`) and strict β:
   - Top, Empty, Nat;
   - Plus A B, List A (parameters);
   - Expr V (parameter V, and a constructor `cst (r : R.R)` depending on
     the module parameter R; recursive);
   - **large elimination** into a universe with strict β: `Fin : Nat -> U l`
     and `Zeros : List -> U l`.
5. **Universes** U l for every level expression, **cumulative**
   (A : U l gives A : U l+ strictly), closed under 1-4 with strict decoding.
6. **Level polymorphism** `[l] ...` in the Theory parameters. It is a family
   of terms indexed by levels: external quantification, so no extra model
   structure.

The Theory parameters then require three *semantic* properties:

7. **Univalence** of each U l (`Axioms[l].Univalence`).
8. **Replacement** (`Images`): for A : U l, B : U k locally U l-small and
   f : A -> B, a chosen image in U l with an embedding into B. The chosen
   image is independent of the elimination level.
9. **Surjectivity** of the chosen quotient map into every proposition family
   over the image, at every level j.

Truncation and set quotients are then derived in Unit (sag/replacement,
`Truncation`, `Completion`). Neither is an interface field.

## 4. The models in the chain

    B  = the base cubical model: presheaves on the poset cube category,
         fibrant types (unit/core, instance L8 posets), T = id.
    P  = PSh(C)_D: the D-modal types over presheaves on the internal category
         C = strictified finitely presented k-algebras (paper Constr. 39),
         D the cobar operation (paper Section 4).
    Z  = the Zariski inner model of P (M5): nullification of a family of
         propositions (paper Example 1 and Section 6.3).

P and Z are both **inner models given by a descent data operation** (paper
Definition 4, Section 2.2.2). So fields 1-3, 5, 7 and the transfer of 8-9
should be proved **once**, for an arbitrary descent data operation on a
model satisfying the interface, and instantiated twice. This follows the
library's method: the abstract statement first, then the instances.
Field 4 (inductive types) is the exception: inductive types are not closed
under modal subuniverses (paper footnote 9: `Nat` acquires constructors
`patch : DN -> N` and `linv`). They need one generic construction too (a
free algebra for the signature plus the patch constructors, in the style of
cavrep Construction 53), covering all six inductive types of Section 3.

Requirement on M5 recorded here: the Zariski step must be presented as a
descent data operation on P (strict lex operation with D eta and eta D
equivalences), so that the generic inner-model theorems apply to it.
