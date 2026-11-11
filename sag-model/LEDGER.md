# M0: assumption ledger

Field numbers refer to `INTERFACE.md` Section 3. Status of each entry:
**exists** (a checked Unit file), **paper** (proved on paper, not
formalised), **todo** (a theorem still needed, with or without a paper
proof), **premise** (a permitted metatheoretic assumption).
Columns: B = base cubical model on posets (T = id); P = PSh(C)_D; Z = the
Zariski inner model. "generic" means: proved once for an inner model given
by a descent data operation on a model satisfying this interface, then
instantiated at P and at Z.

## Metatheory (premises)

| Premise | Where |
|---|---|
| Unit with univalence and funext as segment parameters of the metatheory | as in unit/core (L0); **premise** |
| Universes of the metatheory closed under finite limits, coproducts over small sets, containing finite sets and N (cavrep Assumption 63) | Unit universes and data types; **premise** (check in M1) |
| No excluded middle, no choice, no decidable equality on algebra carriers | ruling; the Delta instance (CClassical) is **not** used |

## Fields

| # | Field | B | P | Z |
|---|---|---|---|---|
| 1 | Π, β and η, strict substitution | **exists**: CPi, CPiE, CPiCart, CPiNat (fibrancy); PresheafPi | generic **todo** (paper 2.2.2: closure of C under Π) | generic |
| 2 | Σ / records, β | **exists**: CSig, CSigNat; PresheafFormers | generic **todo** | generic |
| 3 | Id with strict J-β (Swan) | **exists**: CId, CIdJ, CIdFib, CIdEquiv, CPosId | generic **todo**: modal types closed under Swan Id | generic |
| 4 | Inductive types Top, Empty, Nat, Plus, List, Expr; dependent elimination; strict β including large elimination into U | **todo**: no presheaf instance yet (CwF.seg has only the interface NatStr/ZeroStr/TwoStr); free algebras by cavrep Construction 53 | **todo**: generic construction with patch constructors (paper fn. 9, Remark 30; [CRS19]) | same generic construction |
| 5a | A universe U, closed under 1-4, strict decoding | **exists** for one universe: CUniv, CElC, CSmall, CFibU1-3 (fibrant), at levels a/a+ | generic **todo**: universe of modal types (paper 2.2.2 `ui_C`; modal since D is lex) | generic |
| 5b | Cumulative hierarchy U l for all level expressions, U l in U l+ strictly | **todo**: core has one level step (a, a+; VLift); hierarchy and strict inclusion to state and prove | generic | generic |
| 6 | Level polymorphism | external quantification; no field | — | — |
| 7 | Univalence as the Unit term `Axioms[l].Univalence` | **exists** in ContrOp form: CUaOp, CPosFinal; **todo**: the bridge from ContrOp to the Unit statement | generic **todo** (subuniverse of a univalent universe cut out by a proposition) | generic |
| 8 | Replacement `Images` | **paper**: cavrep §3.4, Theorems 72-73 (Setting 40); **todo** in Unit. Setting 40 holds for the cofibrations chosen in M1.md §1, so Construction 53 applies. CTrunc* (for the old cofibrations) is not reused | generic **todo**: image in the inner model = Σ b. D‖fib b‖, small because D preserves U l; paper Remark 38, footnote 16 | generic |
| 9 | `Surjectivity` at every level j | **paper**: cavrep Theorem 74; **todo** | generic **todo** (elimination into modal propositions) | generic |

## SAG-specific data (for M1-M5, listed for completeness)

| Item | Where it comes from | Milestone |
|---|---|---|
| Base satisfies paper Assumption 1 (connections; ょx × I representable) and cavrep Setting 40 (finite products, decidable homs, cofibrations with finite presentations) | core L1/L8 for posets (CPosC, CPosBase, CSieve, ∀ via the cylinder); to check field by field | M1 |
| Internal free and presented k-algebras, universal properties, k as a parameter | internal construction in B; quotients from replacement (field 8) | M1 |
| C = strictified fp k-algebras (Constr. 39), U ⊣ R, Theorem 21 | paper | M2 |
| Cobar D: fibrancy, descent data operation (Thm 29), levelwise equivalences (Prop 17); Lemma 12 corrected (doc/jonas-model-review.tex) | paper | M3 |
| G and its set-ness (Constr. 45, Prop. 18); coefficient map k -> G | paper | M4 |
| Comparison of the paper's Pr_{T/G,Dκ}, κ = finite sets, with the interpreted `Presentations.Presentation` (`Fin n`, `Expr`) | paper footnote 17 sketches it; **todo** | M4 |
| Presheaf axioms 1-3 (projectivity, duality, N constant) | paper Sections 6.4-6.5 and Appendix A | M4 |
| Zariski step as a descent data operation; Loc, SQC, ZChoice in Z | ~/COLL/SAG.pdf (correct, ruling 2026-11-09); **not formalised** | M5 |

## Open decisions

1. **Inductive types in inner models (field 4).** Proposal: one construction,
   generic over a finitary signature (constructors with parameters, recursive
   arguments, and dependence on a module parameter as in `Expr`'s `cst`).
   It builds the D-modal inductive type as a free algebra including the
   patch constructors, with strict β, and with large elimination into the
   modal universe. The alternative, restating SAGAxioms so that only
   propositional β is used, is rejected: `canonical` and `Zeros` type-check
   only through strict computation.
2. **Universe hierarchy (5b).** Decide between a hierarchy built by iterating
   the core's one-step construction over Unit levels, and a single
   construction parametrised by the level. Strict cumulativity is required
   either way.
3. **Order of work.** The generic inner-model theorems (fields 1-3, 5, 7-9)
   and field 4 are needed by both P and Z. Doing them before M2 means M3 and
   M5 only have to supply a descent data operation.
4. **M5 shape.** Superseded (ruling 2026-11-09): the presheaf-to-sheaf
   argument of `~/COLL/SAG.pdf` is correct; the plan covers only M1-M4.
