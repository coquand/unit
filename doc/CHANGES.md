# `seg/defenv`: a simple checker for Unit, compared with `seg/src`

> **Records (18 October).** Records are now separate from modules, with `new` as their one constructor, an eliminator, and no definitional η; fixed fields are elaborated. `RECORDS.md` is the reference for records; this file has been updated to match it. `core` is migrated (`RECORDS.md` §10).

`seg/defenv` is a parallel copy of the checker:

- `src/`, `app/` and `segd.cabal` build the executable `segd`;
- `segc` runs a server in `core/.segserver-d`;
- `core/` and `examples/` are copies.

The reference is the main checker `seg/src`, as committed on 17 October (3394313), plus one soundness fix made on 18 October (§9). `defenv` is committed (adeb865, branch `gluing-completeness`). The background is in `notes/definitions-and-environments.pdf` and `notes/uniform-evaluation.pdf`.

The aim is the simplest checker that is correct on small examples, following mTT10 and Wang's thesis (`final.pdf`). An optimisation is added only when a measurement shows a need for it.

## 1. Values and environments

- **Definitions.** A group of definitions stays a list of units in the environment (mTT10: `ρ ::= () | ρ, x = u | Dρ`). An access to a definition is the closure `⟨f ; η⟩`, the value `VRef unit η`: the definition as written and the environment of its group. Nothing else is stored, neither the evaluated body nor a list of dependencies.
- **Evaluation never unfolds a definition.** An application of `⟨f ; η⟩` is an ordinary neutral application. Unfolding happens in one place: weak head normalisation under the lock strategy, which is passed to it and never stored in values or in the environment.
- **Declared variables are not bound** (Wang: `()(x) = x`). A parameter or a level evaluates to itself, so it is never part of a dynamic part.
- **Variables of record type.** A declared variable of record type, `c : R[ps]`, is bound by its own frame `EDecl c (VVar c …)`: itself, with its record and head parameters (for its derived members), never dynamic. A fixed field is not a value of the variable: `c.x` is elaborated to the fixed value where it is checked (`RECORDS.md` §11).
- **The dynamic part** of an environment is its `EVar` and `ELvl` bindings. These are the values given by application, by a pattern and by instantiating a segment.
- **Not yet simplified:** a group frame still stores evaluated entries for segments and aliases, a lookup index, and quotation tables (§8).

## 2. Names

The static identity of a piece of code is its occurrence:

- **References.** The resolver writes every reference to a definition, a segment or an alias as its unique id, never by spelling.
- **Occurrences of code.** A `sig` is named by its occurrence (enclosing declaration plus position); a `record` by its declaration. A `split` or a labelled sum is named by its definition and its path (§4). `new` and `struct` are not named: they are constructors.
- **Shadowing.** It is rejected between variables and levels during scope checking (Wang). A variable may still hide a segment, an opened member or a definition, since those are reached through `M.x` or by id.
- **Code identities.** After scope checking, every binder local to an expression (λ, Π, Σ, level λ and Π, pattern variables) gets a unique internal name `x\1id`, and its occurrences follow. The id is never printed.
  - Two closures with the same binder are then the same occurrence of code: the same body, in an environment of the same shape, so they are compared by that name and their dynamic parts, in constant time.
  - Text is never compared. Two closures that are not the same occurrence, for instance those of terms written back for hidden arguments, are compared by ordinary conversion (η: applied to a fresh variable).
  - Segment parameters, levels, record fields and constructor telescopes keep their names.

## 3. Conversion: the rules

These are the rules of this implementation. Rule 2 is our chosen conversion rule. Combined with nominal record types it needs its own justification, so it is not attributed to Wang.

1. **Sufficient rule.** The same static identity and equal dynamic parts give equal values. Dynamic parts are compared position by position, names included. Names matter when two pieces of code have the same text without being the same occurrence: `\ z -> y` under the binders `x y` and under `y x` (test `examples/order.seg`). This holds for closures, splits, sums, record types, Σ-types and accesses to definitions. The dynamic part is the whole environment, not only the variables the code uses.
2. **Same occurrence, different dynamic parts.** For code, the contents are compared:
   - a λ by application to a fresh variable;
   - a split by its branches;
   - a sum by its constructor telescopes.

   Record types are nominal and are never compared by contents: a record type (`record`, `sig`, named Σ) is equal to another only if it is the same declaration or occurrence with equal parameters or dynamic parts. Elements are compared by their constructor: two `new` elements are equal when their record is the same and their parameters and fields are convertible; there is no η.

   For an access to a definition, its body is unfolded under the lock strategy. A locked definition is not unfolded, so two accesses to it with different dynamic parts are different. This is `byDeps` in `examples/locks.seg`, which fails by design.
3. **Different occurrences of nominal forms.** Different declarations or occurrences of a record or Σ-type are different types (Half, Gofer). Rule 3 concerns only these nominal type forms. Different λ-occurrences, for instance, can still be equal by ordinary conversion, and so can `new` elements written in different places.
4. **Folded first.** Conversion first compares folded values. Only the pairs that differ are computed further, by unfolding the definitions that are not `opaque`.

(The earlier question of generative elements against η is settled: `new` is a constructor and records have no definitional η.)

## 4. Restriction on `split` and `data`

A `split` or a labelled sum may only occur at a **definition position**: the body of a definition `f`, after its λs and the branches of its `split`s. Elsewhere, for instance as the argument of a function, the resolver rejects it.

The path from `f` to the occurrence is kept in the occurrence's id. It consists of the λ-variables and, for each branch, the constructor with its pattern variables. A closure `Bρ` is then read back as `f` applied to the values of that path in `ρ` (mTT10 §5: `R(Bρ) = f_B(Rρ)`). `core/` already satisfies the restriction everywhere.

## 5. Read-back never creates a redex

Read-back writes a value back as a term, for hidden arguments and in error messages.

- **λ.** A λ-closure is written under a fresh variable.
- **Split and sum.** A split or sum is written as its definition applied to its path.
- **Application of a definition.** The definition's name is looked up once and applied to the arguments. With no name in scope, the whole application is put in head normal form first, never `(λ…) a`.
- **Definition.** A definition is written by its id if it means the same in the current scope (same dynamic part).
- **Member of a segment.** Otherwise it is a member of the segments its id names, `M1[as1].M2[as2]….f`, written from the innermost segment in scope (same enclosing context).
  - At each level, an instance in scope with the same context and the same parameters is used instead of an application, so `EP.EK.lineL` rather than `CLine[l].EndKit[…].lineL`.
  - The instances searched are the aliases and parameterless segments in scope, then, breadth first, the aliases and segments inside them, each segment entered once, with no depth limit.
  - Only the parameters the value sees are compared: in a segment, a definition sees only the parameters declared before it.
  - A variable is written by its name only if it is a declared variable in scope.
- **Segment type or `new` element.** These are written the same way, ending at the segment itself.
- **Record type.** A record type is re-emitted as its occurrence when its free names mean the same in the current scope. Since records are nominal, this gives the same type only if the dynamic part is also the same.
  - So a record type written inline in a telescope cannot be named once more variables are bound (the reviewer's `pick p`).
  - The remedy in the source is to name it by a definition, `R (A : U a) : U a = sig { val : A }`, so that it is written back as `R A`.

## 6. Inferring hidden arguments (matching)

Matching exists only to infer hidden arguments. It compares the declared type, with holes, against the actual one.

- **Folded view.** Both sides are compared folded. Different heads are first retried after reduction without unfolding any constant: β, projections, splits on constructors, `idJ` on `refl`.
- **Head exposure.** A constant is unfolded only when the other side has a primitive head (Π, Σ, `Id`, a universe, a record or segment type), and only down to that head.
- **Pairs.** A pair pattern against a value that is not a pair uses the projections (η for Σ).
- **Constant against constant.** Nothing is unfolded. The argument must be given explicitly or the statement adapted.

## 7. Error messages

A type error reports the original pair, with no constant unfolded. A definition is printed as `M.f[args]` with its dynamic part, and a variable bound to itself is not shown:

    refl NM.twice x does not prove Id N (Mon.twice[N, one, plus] #0) (Mon.twice[N, zero, plus] #0)
      not convertible (no constant unfolded):  Mon.twice[N, zero, plus] #0   /=   Mon.twice[N, one, plus] #0

## 8. Still to simplify

- **The group frame.** It still keeps evaluated entries for segments and aliases (the sharing of instances), an index by name and id, and, computed once, the dynamic part below it (added after measuring `CDSmallFull2`, where closure comparison recomputed it at every call). `fragOf` searches the entry list once per unit.

## 9. Changes to `core/` (copy in `defenv/core`)

All of these are also valid in the main checker.

- **One constructor function per record** (written when `new` was generative; kept, since `new` is now itself the constructor):
  - `mkPSub`, `mkPEl` and `epsP` in `Presheaf`;
  - `mkSide` and `mkRC` in `CPartial`;
  - `mkXSub` in `CSmall`;
  - `mkPMap` in `CPartial`.
- **Explicit arguments where only unfolding found them:** `CDGlue.aE-S`, and `CLocCompP.PF.At.tn` and `PF.pnat`.
- **No shadowing between variables and levels.** About 170 binders were renamed (`l` → `l0`, `a` → `a0`, `g` → `g'`, …). This is scope checking only.
- **`CLocHorn.vF-compat`.** The lemma `leb-lvl` relates `leb` at levels `a` and `l`. With the full dynamic part, the two instances of `leb` differ; under rule 2 this lemma may no longer be needed.
- **Examples:**
  - `segtypes.seg` states that `NM = NM'` holds (two `new` with equal arguments; it was a `#fails` while `new` was generative);
  - `hidden.seg` uses one constructor `mkBx`;
  - `locks.seg`'s `byDeps` fails by design (rule 2 does not unfold a locked definition).

## 10. Status (small checks)

- **Examples.** All 13 pass except `byDeps` (by design). (Before the records: 9.)
- **Counterexamples.** Every reviewer's counterexample is rejected: closures under different `let`s, records over different types, shadowing, and alias scope.
- **`core`.** Now (after the records): all 202 steps of `runfrom.sh` pass, each under 5 s; the full check in one process takes about 52 s (`RECORDS.md` §12). Before the records, all 199 files passed one at a time, each under 3 s:
  - The slowest were `CPosEl3` (2.9 s; 3.9 s since `new` is compared as a constructor, `RECORDS.md` §12), `CDSmallFull2` (2.4 s; the main checker takes 4.1 s), `CPosEl5` (2.3 s) and `CUaFull1` (2.3 s).
  - These times follow the reviewer's patch (comparing environments in place instead of building lists of values: 4.7 s to 4.2 s on `CDSmallFull2`) and the code identities (4.2 s to 2.3 s).
  - Each time includes about 0.7 s of loading.
- **What the measurements showed:**
  - The slowness of `CPi` and `CIdEquivNat` came from quotation, not from rule 2.
  - First, the old precomputed tables (6.7 s for `CPi`).
  - Then, before aliases inside aliases were found, hidden arguments written as huge explicit paths (250,000 characters in `sdEq`).

## 11. In the main checker `seg/src`, 18 October

- **Soundness fix.** The `eqEnv` speed-up of 17 October skipped the definition groups when comparing closures. It now compares the meanings of the free names (`examples/closures.seg`).
- **Still open there:**
  - the text hash for `sig`/`struct` names;
  - the `eqVal` fall-through that compared two different `new` elements by contents;
  - the exit status of `run-tests.sh`.
