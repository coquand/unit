# Records and modules in Unit (`seg/defenv`): specification

Step 1 of `seg/HANDOFF-records.md`. §§1–4 are implemented (§8, §11). Omitting a fixed field in `new` is deferred (§11).

## 1. Two declarations

    module M (params) { body }
    record R (params) { body }

The body of both is a list of units: declarations `x : A`, definitions `f : A = t`, levels and constraints. A module's body may also contain modules and records. A record's body contains only declarations, definitions and `open` of a module instance.

The two differ in what a declaration in the body means:

- **In a module,** a declaration is a parameter, like a head parameter. `M[args]` gives all parameters, head and body, in order (or by name). This is the current use of `Univ`, `Full`, `CPartial[l].Rel`, ….
- **In a record,** a declaration is a field. `R[args]` gives the head parameters only. The definitions are the record's derived members.

A module is never a type. A record is never instantiated as a module.

**`open` in a record body** is a scope operation: `open M[args]` brings `M`'s members into scope with their own identities (`Objs[obV].Ob`), and creates no field and no copy. Its arguments may use earlier fields; at an element `t`, these are the projections `t.x` (in the environment of the derived members, and in the field types). The normal scope and shadowing checks apply. Test: `examples/recordopen.seg`.

## 2. Modules

- **Instance.** `M[args]` with all parameters given. It is not a value; it is used through `M[args].f`, `module A = M[args]` and `open`.
- **Members.** `M[args].f` is the definition `f` with the dynamic part `args` (rules 1 and 2 of `CHANGES.md` §3 apply unchanged).
- **Records inside modules.** A record declared in `M` may use `M`'s parameters. Its identity is its occurrence together with the dynamic part of the instance, so `M[a].R[ps]` and `M[b].R[ps]` are the same type only if `a` and `b` are convertible.
- **Errors.** `new M[…]`, a variable `c : M[…]`, and `M[…]` with a parameter missing are rejected; the first two with the message "M is a module; declare it with `record` to use it as a type".

## 3. Records

Let `record R (ps : P) { x1 : A1 ; … ; xn : An }` with definitions `d` between the fields. A field type may use the earlier fields and the earlier derived members.

- **Formation.** `R[ps] : U l`, with `l` the join of the field sorts. All head parameters, levels included, must be given.
- **Equality of types (nominal).** `R[ps] = R'[ps']` only if `R` and `R'` are the same declaration (same occurrence, same dynamic part) and `ps = ps'`. Fields are never compared.
- **Construction.** `new R[ps, v1, …, vn]`, positional or by name; only fields, never derived members. It has type `R[ps]` when each `vi : Ai` with the earlier fields set to `v1 … v(i-1)` and the derived members computed from them.
- **Equality of elements.** `new` is the one constructor: two `new R[…]` are equal exactly when their parameters and fields are convertible, wherever they are written.
- **Projection.** For `t : R[ps]`, `t.xi : Ai` with the earlier fields set to `t.x1 …`. β: `(new R[ps, v]).xi = vi`. On a neutral `t`, `t.xi` is stuck.
- **Derived members.** `t.d` is represented as the definition `d` of `R` applied to the element `t`: `R.d[ps] t`. It is a definition like any other: it follows the lock strategy, and its accesses are compared by rules 1 and 2. Unless locked, it unfolds to `d`'s body with each field `xi` set to `t.xi`, whether `t` is built by `new` or neutral. So for `d = value`, an unlocked `p.d` unfolds to `p.value` for any `p`. On `new R[ps, v]` the projections then compute to `v`.
- **Elimination.** `split { R x1 … xn -> b }` on `t : R[ps]`. It binds the fields only; the parameters are those of the type. With motive `C : R[ps] -> U l'`, the branch is checked as `b : C (new R[ps, x1, …, xn])`. β: on `new R[ps, v]` it gives `b` with `x := v`. On a neutral it is stuck.
- **No η.** `t` and `new R[ps, t.x1, …, t.xn]` are not convertible. They are equal in `Id`, by the eliminator (`pty-eta`).
- **`sig` and `struct`.** `sig { fields }` is a record without head parameters declared at its occurrence; `struct { … }` is `new` of it.

## 4. Partially fixed record types `R[ps][x := e]`

A type in which some fields have given values. Written `R[ps, x := e]` as now; only fields can be fixed, never derived members.

- **Formation.** `R[ps][x := e]` is a type when `e : Ax`. So the type of `x` must not depend on a field that is not fixed: every field that `Ax` mentions must be fixed too. Its sort is the join of the sorts of the fields not fixed.
- **Elements.** The same constructor: `new R[ps, v] : R[ps][x := e]` when `new R[ps, v] : R[ps]` and `vx = e`. There is no second constructor. (Deferred: omitting `x` in `new` checked against `R[ps][x := e]`, §11.)
- **Projection.** For `t : R[ps][x := e]`, the projection `t.x` written in the source is elaborated to `e`, at the point where it is checked.
- **Types of projections.** The fixed values also enter the types of the other projections: the type of `t.xi` is `Ai` with each earlier field set to its fixed value if it is fixed, and to `t.xj` otherwise. For

      record Pack { A : U a ; value : A ; }
      p : Pack[A := N]

  `p.value : N`, not `p.A`. The same holds for the types of derived members.
- **Elimination.** The same `split { R x1 … xn -> b }`. A fixed field's pattern variable is bound to its fixed value, not to a fresh variable. The branch is checked as `b : C (new R[ps, …, e, …])`.
- **Equality of types.** `R[ps][F] = R[ps'][F']` when `R[ps] = R[ps']`, the same fields are fixed, and their values are convertible.
- **Subtyping.** `R[ps][F] ≤ R[ps][F']` when every field fixed in `F'` is fixed in `F` with a convertible value; in particular `R[ps][F] ≤ R[ps]`. It is subsumption, with no coercion: the element is the same value. The value of a fixed field may also be read off the element itself, as `subSeg` does now (`new Mon[a, N, …] : Mon[a, N]`).

**Why elaboration, and not a rule of conversion.** The current rule binds a variable `c : R[x := e]` to itself with its fixed fields, so that `c.x` computes to `e`. This depends on `c` being a variable, so it is not stable under substitution. Measured:

    viaVar (M : Mon[a, N]) : Id (U a) M.A N = refl N ;            -- accepted
    viaApp (S : N -> Mon[a, N]) : Id (U a) (S zero).A N = refl N ; -- rejected: (#0 zero).A /= N

The rule `t.x = e` for every `t : R[x := e]` would need the type of every neutral during conversion. Elaborating the projection at the point where its type is known gives `viaApp`, keeps conversion untyped, and is stable under substitution. The price is that a projection *not* written at the fixed type stays stuck: for `pass (M : Mon[a, N]) : Mon[a] = M`, `(pass M).A` is not convertible to `N`. It is equal in `Id`, by the eliminator. Forgetting the refinement forgets its computation; a proof in `Id` keeps the equality. Regression example:

    record Mon (l : Level) { A : U l ; op : A -> A -> A ; e : A ; } ;
    pass (M : Mon[a, N]) : Mon[a] = M ;
    #fails { lost (M : Mon[a, N]) : Id (U a) (pass M).A N = refl N ; } ;
    kept : (M : Mon[a, N]) -> Id (U a) (pass M).A N = split { Mon A op e -> refl N } ;

(in `kept`, `A` is bound to its fixed value `N`, and `pass` unfolds on the `new` element).

## 5. Use in `core`

A rough scan of `defenv/core` found fixed fields only in `new` and in module instances (`Univ[Cl, …]`, `Full[…]`), and no type `R[ps][x := e]` with a body field fixed. Step 3 will confirm this with the new error messages. If it holds, §4 is needed only for the examples (`segtypes.seg`), and can be implemented last.

## 6. Changes from the current implementation, to confirm

1. A module's body declarations are parameters, a record's are fields (§1). Today the same segment can be both.
2. The record pattern binds the fields only, not the parameters. `pty-eta` becomes `split { PTy o h hi ho -> … }`.
3. Fixed fields compute by elaboration of the projection (§4). What is dropped is only the fixed-field meaning of the binding `EDecl c (VVar c fixed)`: a declared variable keeps its scope and its type, and the scope check (no shadowing between variables and levels) stays.
4. Derived members are definitions applied to the element (§3), so they can be locked.

## 7. Order of implementation

1. §§1–3: the `record` declaration, the module/record checks in the resolver, and the record rules in the checker. §4 is deferred; fixed fields stay as they are until then.
2. First small tests, before any migration:
   - constructor β: `(new R[ps, v]).x = v` and `split` on `new`;
   - propositional η: `t = new R[ps, t.x1, …]` in `Id`, by the eliminator;
   - definitional η rejected (`#fails`);
   - an unlocked derived member unfolding on a neutral element, and a locked one not unfolding;
   - the module errors of §2.
3. Then step 3 of the handoff (list `core`'s records), and the migration.
4. §4 last, with the `Pack` and `pass` examples as tests.

## 8. Status (18 October)

§§1–3 are implemented in `defenv/src`:

- **Syntax.** `record R (params) { … }`; `UMod` and `Mod` carry the kind (`SModule`, or `SRecord` with the head parameters). `mkR` is generated for records only.
- **Resolver.** Rejects a module as a type, `new` on a module, a member reached through a record (`R[ps].d`), `module X = R[..]`, `open R[..]`, and modules, opens, levels and constraints in a record body. A record can still be renamed (`module X = R`).
- **Checker.** `R[ps]` needs all head parameters. The eliminator binds the fields only. A wrong pattern says what the fields are.
- **Derived members.** `t.d` is `R.d[ps] t`: the access to `d` in an environment that binds the head parameters, then the element `t` itself, then the fields as `t.x` (not part of the dynamic part). So it is compared by `d`, `ps` and `t`, never by `t`'s fields, and unfolds under the lock strategy, on `new` and on neutral elements alike. The filling pass writes `t.d` as the term `Mem` (record, head parameters, member, element); a variable of record type carries its record, so `c.d` computes the same value directly. Write-back gives `t.d` again. `new R[ps, v]` now has type `R[ps]` (head parameters, not only levels).
- **Fixed fields.** Unchanged and provisional (`EDecl c (VVar c fixed)`, `subSeg`). They do not enter the new rules: record equality is by declaration and dynamic part, and the eliminator takes the head parameters from the type.

Tests:

- `examples/recordrules.seg` (52 declarations): formation, constructor β (fields and derived members), equality of constructions, the eliminator and its β, propositional η, definitional η rejected, nominal records, a record inside a module, derived members unfolding on variables and on neutral applications, a locked derived member not unfolding (also on `new`), `lockedEta` (locked, `b.get` and `(new Box[N, b.value]).get` differ), derived members written back for hidden arguments, and every module/record error.
- `examples/fixedfields.seg`: the current, provisional behaviour of §4. `viaApp` fails (the defect). `lost` is accepted today, because `pass M` unfolds to the variable `M`, which carries its fixed fields; under §4 it becomes `#fails`.
- The other examples are updated (`module` to `record` where a segment is used as a type) and pass, except `byDeps` (by design).

`core` is not migrated yet: every segment it uses as a type is still a `module`, so it now fails at the first one (step 3 of the handoff lists them).

## 9. The segments of `core` used as records (step 3)

`segd All.seg --survey-records` resolves the whole program, with the nesting and parameters of `All.seg`, allowing modules as types. It then lists every segment used as a type or with `new`: its head parameters, its body fields, its derived members, and its uses. The output is `records-survey.txt`.

- **24 segments**, none of them also used as a module: `PCtx`, `PSub`, `PTy`, `PEl` (`Presheaf.Psh`), `SmallCat`, `CwF` and the six `CwF.Formers.*Str`, `Cof`, `LD`, `HEq`, `NMap`, `DConj`, `PMap`, `Side`, `RC`, `SPTy`, `XSub`, `PLine`, `NatMap`.
- **Head parameters and fields** are listed separately for each. Most have no head parameters: their parameters are those of the enclosing module (`Psh (C)`, `Partials (X x)`, …).
- **`open` in `SmallCat` and `CwF`** (`open Objs[obV]`, `open Homs[obV, homV]`, which depend on fields; `open Prelude[l]`, on the head parameter): allowed, see §1. The survey now flags no segment.

`runfrom.sh [-n] START [COUNT]` checks the file-modules one at a time, inside `All.seg` (`--only M`), in the order of its imports with `CBase` expanded (202 steps). It stops at the first failure or at a file over 5 s.

## 10. Migration of `core` (step 4)

The 24 segments of §9 are declared `record` (their parameters stay head parameters, their body declarations are fields). `runfrom.sh Base` passes all 202 steps, each under 5 s; the slowest is `CPosEl3` at 3.8 s.

Definitional η was replaced by propositional η, with conversion unchanged:

- **The eliminator patterns** of `pty-eta`, `psub-eta`, `pel-eta` (`Presheaf`) and `side-eta` (`CPartial`) no longer bind the parameters.
- **New η lemmas:** `xsub-eta` (`CSmall`), `pmap-eta` (`CPartial`).
- **η at the ends of a J proof** (the motive started at `s` while the base case is at `mk s.x1 …`): `CSmall.xs-ext`, `CUniv.EncTy.tyInj`, `CEnc.sideInj`, `CEnc.pmap-ext`. Each now composes the η lemma of the first element, the J proof between constructed elements, and the inverse η lemma of the second.

**More than the planned migration (two cases).** A J proof whose base case needs `B packOf = A` for a type `A : PTy[G]` (`B q` rebuilds a type from `A.tob` and a pack `q`). This is η for the type itself, inside a dependent statement, so composing with `pty-eta` does not suffice. The statement is instead proved for every `A` by the eliminator of `PTy`, whose branch has `A = mkTy G o h hi ho`, where `B packOf = A` holds definitionally:

- `CFibExt.FX`: `core` by `split { PTy o h hi ho -> … }`, and `base` stated for `mkTy G o h hi ho` (stated for a general `A`, `base` was ill-typed, and the failing conversion overran 10 s).
- `COp.OpExt`: `A` is a module parameter, so `core` and `isOpExt` moved to a new module `OpExtE (I ok ob S G)`, with `A` an argument. Three call sites changed: `COpCl` (two), `CDSmallCl` (one, `FX.isOpExt` became `OpExtE[…].isOpExt T1`).

**`CPosEl3` (3.8 s).** This session's record work did not cause the time, but the previous session's did (corrected in §12: `new` as a constructor). The checker before this session's work, on the core before the migration, takes 4.0 s, with the same unfold counts declaration by declaration. It also takes 3.9 s with the committed `Presheaf` and `CPartial`, so the previous session's η lemmas are not the cause either. The 2.9 s of `CHANGES.md` §10 was then an unidentified baseline; §12 identifies it: it predates `new` as a constructor. The time is in four declarations of `Coh.B` (`M.res`, `PmS`, `M.Rs`, `P`, 0.5–0.75 s each), which unfold 34,000–104,000 constants each, mostly `Cat.car`, `CPosC.prodP`, `Cat.mkOb`, `V.Ix`/`Idx` and `GYon.yP`: computation on poset products, not on records.

**Review.** `CFibExt`: the interfaces of `fibExt` and `core` are unchanged; `base` takes the components of a constructed type and is used only by `core`. `core` now computes only on a constructed `A` (before, on `Q = refl` for any `A`); nothing relied on that. This is the expected behaviour of record elimination: it computes on a constructor and is stuck on a neutral element, so a proof by elimination of a record computes only on constructed elements. `COp`: `isOpExt` takes `A` as its first argument, in `OpExtE`; `Pack`, `packOf`, `B`, `Agree` and `base` stay in `OpExt`. The locks are kept (`base` in `OpExt`; `core` and `isOpExt` in `OpExtE`), and no other lock names them.

Diffs and results are in `migration/` (see its README).

## 11. Fixed fields (§4), implemented

- **Projection.** Every projection `t.l` goes through the filling pass (the resolver writes it `ProjU`; before, only projections of non-variables did). There, if the type of `t` fixes `l` (a field, or a head parameter), `t.l` is replaced by the value, written back in the current scope; its type is the field's type. If the value cannot be written back, the projection stays (stuck on a neutral `t`).
- **Variables** of record type no longer carry their fixed fields as values (the old `c : M[x := e]` gives `c.x = e` on a variable only). They keep their record and head parameters, which their derived members need.
- **Types of projections and of derived members** use the fixed values. The *values* of derived members never do, so fixed fields never enter equality: `t.d` stays `R.d[ps] t`, unfolding with `t.x`.
- **Formation.** A field can be fixed only if every field its type mentions is fixed too; the error says which.
- **Deferred:** omitting a fixed field in `new` checked against `R[ps][x := e]`. Nothing uses it, and explicit constructor arguments keep the implementation simpler (the resolver requires every argument of `new`).

Tests: `examples/fixedfields.seg` (23 declarations): `Pack` (`p.value : N`, `p.A = N`), `viaVar` and `viaApp` (both hold now), the type of a derived member at a fixed type, `pass`/`lost` (`#fails`)/`kept`, elements and the fixed value, subtyping both ways, and formation. All examples pass except `byDeps` (by design).

`core`: all 202 steps pass (`migration/runfrom-section4.txt`). The total time is 228 s against 221 s before §4 (+3%, the extra filling pass); the largest increase is 0.23 s (`CLocDUniv`), the slowest file is still `CPosEl3` (4.0 s).

**Baseline.** The examples (`migration/examples-results.txt`, refreshed with §4) and the 202 steps of `migration/runfrom-section4.txt` are the baseline for later changes. The cost of §4 (+3% in total, every file under 5 s) is accepted.

## 12. The full check of `core`: 52 s (investigation)

One process, `segd All.seg` (same build settings, `+RTS -s`):

| checker | core | time | allocated | GC |
|---|---|---|---|---|
| main checker `seg/src` | `seg/core` | 34.2 s | 26.5 GB | |
| `defenv` before the record changes (`Seg.hs.pre-nominal`) | `defenv` core before the η work | 44.8 s | 38.9 GB | 1.0 s |
| `defenv` now | migrated core | 55.3 s (52.3 s without `-v`) | 47.2 GB | 1.0 s |

The "under 30 s" figure is the main checker's (prototype note: 28 s; 34 s today); `defenv` was already at 45 s. Garbage collection is about 1 s in every run, so nothing accumulates in one process: the extra time is computation.

**Cause of most of it: `new` as a constructor.** Bisecting the previous session's changes on `CPosEl3` (same core, `--only`): the nominal change, the removal of the η conversion rules and of the η-expansion of variables change nothing; dropping the occurrence name of `new` (`SegParse`, `named rs (New m)`) multiplies the unfoldings by 3–4 (`Coh.B.P` 19,309 → 64,017; `CPosEl3` 2.84 → 3.86 s). Same for `CTrP` (1.24 → 2.22 s), `CPi` (1.74 → 2.40 s), `CPosEl5` (2.18 → 2.61 s), `CIdFib` (1.46 → 1.90 s). With occurrence names, two `new` elements of different occurrences were unequal at once; as a constructor, `new` is compared by its arguments, and when they differ (`Y` against `Z` here: 17,161 such comparisons against 2,021) each failed comparison unfolds deeply before it fails. The comparisons that succeed are as cheap as before.

The rest (about 3 s) is of the order of the §4 cost (+3%).

Not changed: the constructor rule is the design (§3). Possible remedies, not tried: compare the arguments of two accesses to the same definition (`sameDef`) without unfolding first, and unfold the heads when that fails (keeping full comparison for locked heads), so that a failing argument comparison is cheap.

## 13. Tried: unfold instead of converting the arguments (negative)

`sameDef` (two accesses to the same unlocked definition are equal when their arguments are convertible) was removed, so that conversion compares arguments only structurally (`eqVal`) and otherwise unfolds; a locked definition still has its arguments compared by conversion (`conv'` on the weak head normal forms). The examples pass (`byDeps` aside), but every file of `core` tried (`CPosEl3`, `CTrP`, `CPi`, `CPosEl5`, `CIdFib`) overran 30 s, against 1.5–4 s with `sameDef`. Comparing the arguments by conversion is what keeps the successful comparisons cheap: unfolding instead re-does the work inside the bodies, at every level. Reverted.

So the cost of §12 is in the comparisons that fail, and a remedy must keep argument conversion for those that succeed.

**Decision (18 October).** Constructor equality and `sameDef` stay; the cost of §12 (about 17% of `defenv`'s full check) is accepted. No caches or heuristics without a simpler, well-supported idea.

## 14. Why the elaboration of fixed fields is sound and stable (a semantic sketch)

This is a sketch of semantic soundness, not a syntactic preservation proof. It assumes two things it does not establish: a model in which the refinement equations of `R[ps][F]` hold, and that the read-back writes a value as a term with the same meaning. The remark that a missing equation only makes conversion incomplete explains why conversion may ignore these equations; it does not prove either assumption.

**Reading of the types.** `R[ps][F]`, with `F` a list of fixed fields `x := e_x`, is read as the type of the elements `u` of `R[ps]` such that `u.x = e_x` for each `x` in `F`. The equations hold in the reading (the model), not in the checker's conversion, which never uses them. Conversion only has to be sound for this reading, not complete, so a conversion missing an equation of `F` is an incompleteness, never an unsoundness.

**The elaborated term is well typed.** For `t : R[ps][F]` and `x` in `F`, the projection `t.x` is replaced by `e_x`, with the type `A_x` of the field. Formation checked `e_x : A_x` with the head parameters `ps` and the earlier *fixed* values, and required every field that `A_x` mentions to be fixed. So `A_x` does not mention `t`, and `e_x` has the type that `t.x` has. In the reading, `t.x = e_x`, so the replacement does not change the meaning.

**Dependent field types.** A later field `y` has type `A_y` with each earlier field set to its fixed value if it is fixed, and to `t.z` otherwise. In the reading `t.x = e_x`, so this type is equal to the one with `t.x` everywhere. The checker computes types only by the typing rules, never from unfolded values, so it always uses this form. A term typed at the larger type `R[ps]` gets the form with `t.x`; meeting both forms in one comparison can fail, but that is incompleteness. It is the case of `lost` (§4).

**Derived members.** At `t : R[ps][F]`, the *type* of `t.d` is computed with the fixed values (as for fields), and its *value* is `R.d[ps] t`, which unfolds with `t.x`. In the reading the two agree, since `t.x = e_x`. The value never depends on `F`, so fixed fields never enter equality, and two uses of `t.d` at different refinements of `t`'s type are the same value.

**Stability under substitution.** Elaboration happens once, where the projection is checked, and leaves `e_x` in the term. The checked terms contain no rule that depends on a variable carrying fixed fields: substituting an element `u : R[ps][F]` for a variable gives the same `e_x`. This is what failed before, when only a *variable* computed its fixed fields (`viaApp`).

**Elements and subtyping.** `new R[ps, v] : R[ps][F]` is checked by `v_x = e_x` for `x` in `F`, so constructed elements satisfy the reading. A neutral element has the refinement only through its type, which the reading takes as given. `R[ps][F] ≤ R[ps][F']` for `F'` contained in `F` (with convertible values) is inclusion of these subsets; subsumption changes no term.

**Elimination.** The branch of `split { R x1 … xn -> b }` at `R[ps][F]` binds a fixed field to its value, and is checked at `new R[ps, …, e_x, …]`. On an element `new R[ps, v]` of `R[ps][F]`, `v_x = e_x`, so β gives a term of the expected type.

**Writing back.** The value `e_x` is written in the current scope by the read-back, which only produces a term meaning the same value there. When it cannot, the projection is kept: sound, only less informative.
