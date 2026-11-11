# sag-model: a model of synthetic algebraic geometry in Unit

Plan: `../../doc/sag-model-plan.pdf` (milestones M0-M6).
Paper followed: Coquand-Höfer-Sattler, *Constructive higher sheaf models
with applications to synthetic mathematics* (34-page version in Höfer's
thesis, `~/COLL/jonas.pdf`; numbering below refers to it). Replacement in
cubical models: Cavallo-Coquand, `~/COLL/cavrep.pdf` (TYPES 2025).

## Goal and rulings (2026-11-09)

- The goal is the first endpoint, M0-M5: a checked semantic inhabitant of
  the interpreted `sag/affine/SAGAxioms.seg` `Assumptions`, with the Theory
  parameters of `sag/affine/All.seg` (univalence, images, surjectivity)
  discharged in the same model. M6 (interpreting the Picard proof) waits.
- Ruling (2026-11-09): the passage from the presheaf model to the sheaf
  model in `~/COLL/SAG.pdf` is correct.  The formalisation plan covers only
  M1-M4 (base model B, the site C, the presheaf model P, the presheaf
  axioms in P); M5 is not formalised and not re-settled on paper.
- No dependent or countable choice is used, so the base modality is T = id:
  the base is the cubical model itself, and κ is the finite sets (`Fin n`).
- Set quotients come from propositional truncation, and truncation from
  replacement, as in `sag/replacement`. No higher inductive types in Unit.
  (Semantic free-algebra constructions inside the model are allowed; they
  are how the model justifies the source's inductive types.)
- No decidable equality of algebra carriers, in k or in presented algebras.

## Files

- `INTERFACE.md` (M0): the source fragment the endpoint uses, obtained by
  auditing the statement of `SAGAxioms.Assumptions`, and the structure a
  model must supply to interpret it, with the required strictness.
- `LEDGER.md` (M0): the assumption ledger. One row per interface field, for
  each of the three models in the chain (base cubical model B, presheaf model
  P = PSh(C)_D, Zariski model Z), saying what exists, what is still to prove,
  and what is a permitted metatheoretic premise.
- `M1.md`: decisions for M1, the check of the poset base against paper
  Assumption 1 and cavrep Setting 40, and the work order.

- `All.seg` (check: `./segc sag-model all` from unit/): core files are
  symlinks to ../core (read-only); `PosCof`, `PosCofAll`, `PosCofConj` are
  M1 step 1 (`PosCofEq`: equaliser cofibrations) (the cofibrations of M1.md §1). `PosFull` (the base instance
  `CBase.CB` at these cofibrations), `PosId` (Swan Id) and the shim
  `CPosInst` are M1 step 2: the shim makes the symlinked core files
  CPosEl1-5, CPosFinal re-instantiate at `PosFull` (M1.md "Status of
  step 2"). Do not replace `CPosInst.seg` by a symlink. `CwFCl`,
  `FibCwF`: M1 step 3 (the interface at B); `PosJNat`: J commutes with
  substitution; `PosIdY`, `PosIdYFib`, `PosIdYJ`: the Yoneda Id, its
  fibration and J; `CwFId`: the Swan Id record of the interface;
  `FibIdRd` (reading transported Yoneda-Id elements), `FibIdCen`,
  `FibId`: its instance `FibId.fibId` at the fibrant types (all these
  `level a l`: base level a, presheaf level l).  `FibClL` (Fib at level
  l), `CwFU` (the universe record, and `UnivUa.UaStr`, the field
  UaContr), `FibUniv` (its instance at `FibCwF[a, a+]`).
- The univalence bridge, generic in a CwF with Pi, Sigma, Swan Id
  (M1.md "Step 3, the univalence bridge"): `CwFOv` (stability calculus:
  over-paths along any substitution), `CwFEq` (S1: isContr, Htpy, RetT,
  isEquiv, Equiv, bi-invertible as the source's, with stability),
  `CwFInt` (pairs, projections, application, eta for maps into an
  extension, the identity equivalence), `CwFJ` (J at a point),
  `CwFContr` (a contraction normalised at a point), `CwFUaEq` (S5:
  UaContr gives isEquiv idtoeqv).
- S4 (M1.md "Step 3, S4"): generic toolkit `CwFTr` .. `CwFS4`, the
  wrapper `CwFUaW`, `CwFCC` (isContr A contractible; Kr a proposition).
  At B: `FibNF` (naive funext; `LineY`: a natural line field is a Swan
  Id element), `FibContr` (S2: core ContrOp gives internal isContr),
  `FibHt` (Swan homotopies are core homotopies; internal isContr gives
  a ContrOp).  `CLocBoundContr`, `CLocBoundRetr`: symlinks to core.
  S3 (core equivalences = contractible fibres, both ways, at any
  context): `CwFFv`, `FibYC`, `FibC2`, `FibS3`.  uaC0 from `CPosFinal.ua`
  in progress (M1.md "Step 3, S4: the B inputs").

## Status

M0: interface and ledger written (2026-11-09).
M1 step 1 checked (2026-11-09): cofibrations of type (2) with all fields
of `CBase.CB`, ∀ and dependent conjunction (M1.md "Status of step 1").

M1 step 2 checked (2026-11-09): `CBase.CB` instantiated at the new
cofibrations, Swan Id, universe fibrant + univalence (`CPosFinal[a].ua`,
`fibU`) at the new base (148 modules, 0 failed, 23 s, max file 2.0 s).

M1 step 3 in progress (2026-11-09): `CwFCl` (generic CwF of structured
types, Pi/Sigma transfer) and `FibCwF` (fibrant types of B with Pi,
Sigma) checked; 150 modules, 0 failed, 23 s.

`PosJNat` checked (2026-11-09): J commutes with substitution (`JN.jnat`);
151 modules, 0 failed.

Swan Id (2026-11-09, ruling: Yoneda-presented Id): `PosIdY` (the type,
strictly stable: `IdYNat.nat`), `PosIdYFib` (with its fibration, natural),
`PosIdYJ` (J, beta, J natural), `CwFId` (the generic record). 155 modules,
0 failed.

Swan Id instance (2026-11-09 night): `FibId.fibId :
CwFId.SwanId[a+, fibCwF].IdJStr` checked (Id, refl, J, strict beta, all
natural; 158 modules, 0 failed; FibIdCen 7.3 s, FibId 5.0 s with load).
See M1.md "Step 3, Swan Id instance".

Equaliser cofibrations (2026-11-09 night): `PosCofEq.EqC[X, Y, f, g].eqS`
= {f = g} for any f, g : X -> Y, with `lands-eq` / `eq-lands` (h lands iff
f h = g h) and stability `eq-pre`; 159 modules, 0 failed.

Universe (2026-11-09 late night): the FibCwF / Swan Id files are generic
in the presheaf level (`level a l`); `FibClL` (Fib at level l), `CwFU`
(the record `Univ[l, C].UnivStr`: Cod, Cod-nat, Dec, Dec-nat) and its
instance `FibUniv.fibUniv` at `FibCwF[a, a+].fibCwF`, from core's universe
of level-a fibrant types.  162 modules, 0 failed.  See M1.md "Step 3, the
universe".

Univalence bridge, generic part (2026-11-09, late): S1 (`CwFEq`), the
field UaContr (`CwFU.UnivUa.UaStr`, with the source's bi-invertible
Equiv, ruling of the day) and S5 (`CwFUaEq.UaEq.At.ua`: in any CwF with
Pi, Sigma, Swan Id and a universe with UaContr, idtoeqv a b is
bi-invertible) checked. 168 modules, 0 failed, 35 s; the seven new files
together 0.6 s. See M1.md "Step 3, the univalence bridge".

**Next:** S2-S4 (UaContr at `FibCwF[a, a+]` from core's ContrOp; needs
isEquiv_bi to be a proposition in the model, i.e. semantic funext); codes
for Pi, Sigma, Id; cumulativity with the hierarchy. (The Zariski step is
out of scope: ~/COLL/SAG.pdf, ruling above.)
