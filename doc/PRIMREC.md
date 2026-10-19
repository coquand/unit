# Recursion only through eliminators: design

Status: design, 19 October 2026; §5 revised after review (operational details). Nothing is implemented yet. The survey
behind it is `migration/primrec-survey.txt` (`segd All.seg --survey-primrec`).

**Central invariant.** Every recursive computation starts from an eliminator
(`split` on a data type), and the checker constructs that eliminator's
recursive results. Recursion by name does not exist: no definition, at any
level, can refer to itself or to a later definition.

## 1. Scope: sequential everywhere

- A definition sees only the units before it: earlier definitions,
  parameters, modules and instances. This holds at top level, in module and
  record bodies, in `let` and `where`, inside types, and inside `#fails`
  blocks. A definition does not see itself, and does not see a later member
  of what used to be its group. Mutual groups disappear.
- **The one exception is a data type**, which sees its own name in its
  constructor fields, and only there (not in its own type, not in its
  parameters).
- A `where` local sees the parameters of its definition and the earlier
  locals, but not the definition itself.
- A violation is a resolver error ("not in scope", with a hint that recursion
  goes through `split`). Inside `#fails` it is a failure of the block, as
  resolution errors already are.

The scope rule alone removes every cycle among ordinary definitions. There is
no traversal to trust: a name that is not in scope cannot be referred to,
wherever it occurs (types, constructor fields, `let` in types, module
arguments, directives).

The restrictions R1 and R2 of `Term.hs` become consequences of this rule and
are dropped. A `let` in a type can't be recursive. A constructor field can
mention only earlier definitions and its own data type.

## 2. Data types

- **Uniform parameters.** `data D (ps : Δ) : U l = c₁ tel₁ | …`. In a field,
  `D` occurs only applied to exactly its parameters, in order: `D ps`, as
  variables, with the same level arguments if any. A data type in a module
  uses the module's parameters freely; they are not parameters of `D`.
- **Recursive fields.** A field is recursive when its type, after the earlier
  fields, has the shape
  - `D ps` (first order), or
  - `(ys : Ψ) → D ps`, where `Ψ` does not mention `D` (a function field, as
    in `sup (A : U l) (f : A → M)`).
- **Any other occurrence of `D` in a field is rejected.** This includes the
  domain of a function, an argument of another type (`Plus D D`, nested
  types), and a mention under any other type former. This is strict
  positivity restricted to these two shapes. Since fields can't mention later
  definitions, no alias can hide an occurrence.
- **Mutual data types are excluded** in this version. They can't be
  expressed, because a data type sees only itself. Simultaneous eliminators
  can be added later if needed. `core` has none.
- **Records** are not recursive: a record can't name itself inside its body,
  and its `split` binds fields without recursive results.

## 3. Branches and their typing

**Syntax.** A branch may bind, after its pattern variables, one name per
recursive field, in order of the fields:

    c x₁ … xₙ | r₁ … rₖ -> e

- The whole `| r₁ … rₖ` list may be omitted, which is the current syntax;
  the branch then can't use its recursive results.
- When the list is present it must have full length, one name per recursive
  field. `_` names a result that is not used.

**Typing.** A split is checked against a function type `(x : D ps) → P x`,
where `P` is a closure (the motive).
- Everything after `x` is inside `P`. In `ack : N → N → N`, the motive of the
  outer split is `P x = N → N`.
- The arguments before the split are *fixed*. They are the lambdas around the
  split, together with the variables of enclosing branches, and they are in
  the split's environment. A recursive result is always the *same* split
  applied to a field, so fixed arguments can't change. A recursive call that
  changes one, like `max-or (\ v -> P (suc v)) j k` with `P` before the
  split, has no recursive result. The fix is to move `P` after the split.

In the branch for `c`, with the fields `xs : tel` instantiated at `ps`:

| field | its recursive result |
|---|---|
| `xᵢ : D ps` | `rᵢ : P xᵢ` |
| `xᵢ : (ys : Ψ) → D ps` | `rᵢ : (ys : Ψ) → P (xᵢ ys)` |

The branch body is checked against `P (c xs)`, as now. For records, the
single branch is unchanged.

## 4. Nested splits, worked through

**`skipN`.** The inner split takes the next argument. Its recursive results
are the inner ones, and the outer result, a function, is available in the
inner split.

    -- now
    skipN : N -> N -> N = split {
      zero -> \ n -> suc n ;
      suc k -> split { zero -> zero ; suc n -> suc (skipN k n) } } ;

    -- with eliminators: r : N -> N  is  skipN k
    skipN : N -> N -> N = split {
      zero -> \ n -> suc n ;
      suc k | r -> split { zero -> zero ; suc n -> suc (r n) } } ;

The inner split is checked against `N → N` in the branch `suc k`. The
outer motive is `P x = N → N`, so `r : P k = N → N`.

**Ackermann.** Rebuilding `suc m` does not justify a call by itself. The call
`ack (suc m) n` is recursion of the inner split on `n`, so it becomes the
inner recursive result.

    -- now
    ack : N -> N -> N = split {
      zero -> \ n -> suc n ;
      suc m -> split { zero -> ack m (suc zero) ;
                       suc n -> ack m (ack (suc m) n) } } ;

    -- with eliminators
    ack : N -> N -> N = split {
      zero -> \ n -> suc n ;
      suc m | r -> split { zero -> r (suc zero) ;
                           suc n | s -> r s } } ;

- Outer split: motive `P x = N → N`, so `r : N → N` is `ack m`.
- Inner split, in the branch `suc m`: its type is `N → N`, with motive
  `Q y = N`, so `s : Q n = N` is the inner split applied to `n`, that is
  `ack (suc m) n`.
- `ack m (ack (suc m) n)` becomes `r s`.

This is higher-type primitive recursion: the result of the outer recursion
is a function.

## 5. Computation, conversion, read-back

### 5.1 Certified recursive fields, stored in the checked term

`app` receives only the split and the constructor value, so it can't know
which fields are recursive. Evaluation must not guess this from the shape of
values. Instead, the information is computed once, from the data type, and
stored in the term.

- **Where it comes from.** The data definition's constructor telescope
  (`Sum`), checked by §2. For each constructor `c`, the list
  `recs(c) = [(j, n)]` gives the position `j` of each recursive field and the
  number `n` of its function binders: `n = 0` for `D ps`, `n = |Ψ|` for
  `(ys : Ψ) → D ps`. It is computed syntactically from the field types, which
  §2 has already checked to have exactly these shapes.
- **Where it is stored.** The filling pass already rewrites every split
  against its scrutinee type (`VSum t _ cs r`). It now also annotates each
  branch:

      Split Id [(Name, ([Name], [Rec], Exp))]
      data Rec = Rec Int Int Name    -- field position, number of binders, result name

  An omitted `| rs` list gives result names that the body can't refer to.
  The resolver checks a present list for full length, and the filling pass
  checks it against `recs(c)`. A record split gets `[]`.
- **The annotation runs on every split, not only on terms with holes.**
  The filling pass skips a term without hidden arguments (`fillC` returns
  it unchanged). So a split with an unannotated result (position `-1`)
  counts as a term to fill (`hasHole`), and the pass reaches it in every
  definition, fully explicit ones included.
- **Evaluation reads only the annotation.** It never inspects types or
  values to decide what is recursive.

### 5.2 Constructor reduction

The only new rule is in `app f@(VSplit t d bs ρ) (VCon c vs)`, for the
branch `(c, (xs, recs, e))`. The body `e` is evaluated in `ρ`, extended by
`xs := vs` and, for each `Rec j n r` in `recs`:

- if `n = 0`: `r := app f (vs !! j)`, which is lazy;
- if `n > 0`: `r :=` the lambda closure
  `⟨λ y₁ … yₙ. ρ_t (x_j y₁ … yₙ) ; ρ, xs := vs, ρ_t := f⟩`.

The bound names are internal and fresh: `ρ_t` and the binders `yᵢ` are
written with the code-identity separator (`\1`) and the split's occurrence
`t`, constructor `c` and field `j`. This matters because `eqClos` treats two
closures with the same binder as the same code. Since the generated body is
determined by `(t, c, j, n)`, that treatment stays sound. The names can't
clash with `%self`, which the record members use, or with any source name.

Record β is unchanged, with no recursive results. `whnf` gets no new case,
because a recursive result is an ordinary application or closure.

### 5.3 Conversion of splits

Today two splits with the same occurrence `t` are equal when their dynamic
parts are convertible, or else when their branch bodies are convertible
under fresh variables for the pattern variables (`Seg.hs:817`).

- **Pattern variables and recursive results are both fresh.** In the
  fallback, both get fresh generic variables (`VGen`).
- **Binding the recursive results to actual calls would not terminate.**
  `r := app f₁ x` against `r := app f₂ x` with `x` a generic variable gives
  `VApp f₁ x` against `VApp f₂ x`. That compares `f₁` with `f₂` again, so
  the fallback starts over.
- **Fresh results keep the fallback structural.** It compares two pieces of
  code under variables, and terminates as the current fallback does.
- **Justification.** If the bodies agree for all fields and all recursive
  results, then by induction on the argument the two eliminators agree on
  every constructor value. Both satisfy the same recursion equations, and
  the initial algebra (W-type) has a unique map with given equations, in
  the set and presheaf models alike. So the fallback is the uniqueness of
  the eliminator, restricted to two occurrences of the same code.
- **The alternative** is to remove the fallback. That loses the equalities it
  gives today: two occurrences of the same split whose environments differ
  only in variables the branches don't use (locks.seg's `byDeps`, and lemmas
  instantiated twice).
- **Proposal.** Keep it with fresh results, and count how often it fires in
  the prototype and on `core`. If it rarely matters, removing it is the
  simpler rule; that decision is left for after the measurement.

### 5.4 Read-back

The quotation writes a sum or split value `VSplit t _ _ r` as its definition
applied to the values along its path (`byPath`, `Seg.hs:2622`), for example
`ack (suc m)` for Ackermann's inner split. With recursive results, that is
correct only when the split's environment is the one obtained by evaluating
the definition along that path, so that its recursive results are the
canonical ones.

- **Split values with abstract results do exist.** Checking a branch never
  evaluates the unnamed split in it, but the conversion fallback (§5.3)
  evaluates branch bodies under fresh variables for the recursive results.
  When such a body is a nested split, the result is a split value with an
  abstract `r`. These values are allowed internally.
- **So the safeguard below is essential, not defensive.** The text of the
  reconstruction is the same in both cases (`ack (suc m)`); only the check
  of the recursive results tells them apart.
- **Named local splits** (a `where` helper inside a branch, which may use `r`)
  are values during checking, with `r` abstract. They are read back through
  their own name. Their `VRef` carries their whole environment as its
  dynamic part, including `r`, and the name is used only when that dynamic
  part is convertible with the one in scope (as now). Their own path starts
  at their own definition, so it never goes through the abstract `r`.
- **The safeguard.** For each `Rec` of a branch on the path, `byPath`
  compares the result bound in `r` with the canonical value: the prefix of
  the path, evaluated and applied to the field. If they differ, `byPath`
  returns `Nothing` and the value is not written back, which is how
  quotation already reports a value it can't name. This costs one
  conversion per recursive result on the path, and only at read-back.
- **Enclosing definition out of scope.** As now: `byPath` quotes the
  definition's name without unfolding. If the name can't be reached from the
  scope at the quotation point, through the segment paths and aliases
  `segPathIn` already searches, the result is `Nothing`. Recursive results
  add no new case: they are written back through the split they apply.
- **Escaped closures.** A closure for a function field
  (`r = λ a. ρ_t (f a)`) is read back as a lambda whose body is the split
  applied, `\ a -> liftM (f a)`, which is the source form.

### 5.5 Recursive results under locks

**The rule.** Locks control the unfolding of names, and only that.
- `whnf` and conversion do not unfold a locked name.
- An eliminator value that has already been produced keeps its
  computation rules: a split applied to a constructor reduces, and its
  recursive results are applications of that split, whatever the locks.
- Values are lock-agnostic, as now: `eval` never consults the lock.

A recursive result of `g` is produced only by reducing a split value of
`g`, and that value comes from unfolding `g`.
- `eval` of the name gives the closure `VRef`.
- Checking paths that compare without locks, such as the second test of a
  hidden argument in `fillSpine`, may unfold `g` and so produce its
  recursive results inside that comparison. That is allowed by the rule.

What this does not claim: equivalence with today's recursion by name in
every checking path. It is tested instead (`examples/primrec.seg`):
- a locked `dbl` and a locked `copy` no longer compute through their
  names;
- `cw1 = copy w1`, defined before the lock, is stuck after it, since it is
  unfolded only when used;
- an eliminator not reached through the locked name (`copyL`) computes.

### 5.6 Termination (sketch)

- Unfolding names terminates, because definitions are well ordered by the
  scope.
- `Sum` values are lazy and are never unfolded by recursion.
- A split reduction calls the split again only through a recursive result,
  on a recursive field of the constructor value. With strict positivity and
  uniform parameters, the data types are inductive (W-types with
  parameters), and the eliminator is the standard dependent one.
  Normalisation of the whole calculus is the standard argument for MLTT
  with W-types, universes and these eliminators.
- The conversion fallback (§5.3) compares code under fresh variables, and
  terminates as today.
- **Outside the scope of this sketch.** A context whose level constraints
  have a loop collapses (Gonthier's rule: everything converts), so it can
  type non-terminating terms. That is an existing property of the universe
  system, unrelated to recursion.

## 6. Worked migrations

**A W-type definition** (`VLift.liftM`, `V.isIt`). For `sup A f`, the result
for `f : A → M` is `r : (a : A) → P (f a)`.

    liftM : V0.M -> W.M = split { sup A f -> sup A (\ a -> liftM (f a)) } ;
    -- becomes
    liftM : V0.M -> W.M = split { sup A f | r -> sup A r } ;

    isIt : M -> U l+ = split { sup A f -> isEmb A f * ((a : A) -> isIt (f a)) } ;
    -- becomes
    isIt : M -> U l+ = split { sup A f | r -> isEmb A f * ((a : A) -> r a) } ;

Later statements such as `isProp-isIt`, `lift-isIt` and `lift-refl` mention
`liftM (f a)` or `isIt (f a)` by name in their types. `r a` is convertible
with these by unfolding (§5.5), as `liftM (f a)` and its unfolding are
today.

**A helper cycle** (`Sum.cnt-le` / `cl1`). The helper is declared first and
takes the recursive result as an argument.

    -- now: cnt-le calls cl1, and cl1 calls cnt-le p m
    cnt-le (p : Nat -> Bool) : (m : Nat) -> IsT (leb (cnt p m) (suc m)) = split {
      zero -> cl0 (p zero) ;
      suc m -> cl1 p m (p (suc m)) } ;
    cl1 (p : Nat -> Bool) (m : Nat) : (b : Bool) -> IsT (leb (plus (cnt p m) (b2n b)) (suc (suc m))) = split {
      true -> … (cnt-le p m) ;  false -> … (leb-step (cnt p m) (suc m) (cnt-le p m)) } ;

    -- with eliminators
    cl1 (p : Nat -> Bool) (m : Nat) (ih : IsT (leb (cnt p m) (suc m)))
      : (b : Bool) -> IsT (leb (plus (cnt p m) (b2n b)) (suc (suc m))) = split {
      true -> … ih ;  false -> … (leb-step (cnt p m) (suc m) ih) } ;
    cnt-le (p : Nat -> Bool) : (m : Nat) -> IsT (leb (cnt p m) (suc m)) = split {
      zero -> cl0 (p zero) ;
      suc m | r -> cl1 p m r (p (suc m)) } ;

The other eleven cases are migrated the same way. `CLocD`'s
`miss`/`fg`/`cases` group also needs `fg` moved after `miss`. `max-or` moves
`P` after `j k` (one outside call site).

**`lift-refl`.** This is the one substantive case. Today `lift-refl` and
`lr-fwd` are mutually recursive, and the call `lift-refl (g b) … (f a) …`
has its arguments swapped. With eliminators, the recursion is on `x` alone,
and `y` is in the motive:

    P x = (ix : isIt x) (y : M) (iy : isIt y) -> Id (liftM x) (liftM y) -> Id x y
    r   : (a : A) -> P (f a)         -- in the branch  sup A f

The inner split on `y` (`sup B g`) needs no recursive result.
- Forward direction, `a : A`: `memT … P a` gives `b : B` and
  `Q : Id (liftM (g b)) (liftM (f a))`. The witness needed is
  `Id (g b) (f a)`, which is `sym (r a (ix.2 a) (g b) (iy.2 b) (sym Q))`.
  The swap is undone by symmetry of `Id`.
- Backward direction, `b : B`: `memT … (sym P) b` gives `a'` and
  `Q' : Id (liftM (f a')) (liftM (g b))`. The witness is
  `r a' (ix.2 a') (g b) (iy.2 b) Q'` directly.

`lr-fwd` becomes a non-recursive helper declared before `lift-refl`, taking
`r` as an argument; it is used for both directions.

## 7. Migration and checking order

1. Implement scope (§1), branch syntax and typing (§3), the annotation and
   evaluation (§5.1–5.2), conversion (§5.3) and read-back (§5.4).
   Keep positivity from `Term.hs`, restricted to the shapes of §2. Delete
   the size-change pass; `--survey-primrec` stays as a migration aid until
   the migration is finished.
2. A small prototype and small tests before `core`:
   - `plus`, `skipN`, `ack`, a W-type (`isIt`-like), `cnt-le`/`cl1`, and a
     small `lift-refl` on a toy W;
   - read-back: of `ack (suc m)`, of `liftM (sup A f)` (escaped closure),
     and of a `where` helper that uses `r`; a lock on `liftM` (§5.5); the
     fallback counter (§5.3);
   - `#fails` for self-reference, a forward reference, a reference in a
     type, a reference in a constructor field to a later definition, a
     partial `| rs` list, a negative field, a non-uniform parameter, and a
     changed fixed parameter (the `max-or` shape).
3. Migrate `core` in dependency order with `runfrom.sh` from `Base`,
   stopping at the first failure or a file over 5 s.
   - The 161 direct cases are *candidates* until their transformed terms
     type-check.
   - Then come the 12 reorderings or helpers, the 22 forward references,
     and `lift-refl`.
   - Any case needing more than §6 is reported, not forced.

## 8. Decided, and still open

Decided:
- The whole `| rs` list may be omitted. When present, it has full length.
  `_` is allowed.
- The definition-position restriction for `split` is kept.

Open:
- Whether to keep the conversion fallback (§5.3). This will be decided by
  measuring how often it fires in the prototype and on `core`.

## 9. Prototype status (19 October 2026)

The prototype is in `seg/primrec`, a copy of `defenv`; `defenv` and its
`core` are unchanged.
- **Implemented:**
  - sequential scope (`SegParse.sequentialDefs`);
  - the branch syntax `c xs | rs -> e`;
  - positivity with uniform parameters (`Term.fieldError`);
  - the annotation `RecR j n r`, forced by `hasHole`;
  - typing (`recCx`) and constructor reduction (`recBind`);
  - the conversion fallback with fresh variables, counted;
  - the read-back safeguard (`byPath`);
  - `--quote-test`.
- **Fixed along the way** (also present in `defenv`): the paths of splits
  and sums were computed before binders were renamed. So `byPath` looked up
  source names that the environment does not bind, and failed for any
  split under a lambda or a pattern variable. Paths are now computed after
  renaming (`pathUnits (binderUnits ..)`).
- **`examples/primrec.seg`, 53 declarations, all pass:**
  - `plus`, `skipN`, Ackermann, a dependent motive, a helper taking `ih`,
    a W-type with an escaped result read back as `\ y -> copy (noW y)`;
  - the fallback on a nested split (fired 3 times);
  - locks;
  - 10 `#fails` (self-reference, forward reference, reference in a field,
    partial or extra results, a negative field, a non-uniform parameter, a
    changed fixed parameter, a record).
- **`--quote-test ack`** gives `ack (suc m)` with the canonical results, and
  is refused with abstract ones. The same holds for `skipN`.
- **The `defenv` examples:** the 10 without recursion by name pass
  unchanged. The 4 with recursion by name (`basic`, `locks`, `segtypes`,
  `termination`) are scope errors until migrated.



## 10. Migration of core (19 October 2026)

**Result.** All 202 steps of `runfrom.sh` pass, and so does the full
check: 11816 declarations, 0 failed. The details are in `migration/`.

**Examples.** The four example files that used recursion by name are
migrated: `plus` in `basic`, `locks`, `segtypes`, plus `termination`.
- Two changes go beyond direct replacement. `even`/`odd` become one
  eliminator computing the pair. `half` becomes course-of-values recursion,
  computing the pair `(half n, half (suc n))`.
- `locks.seg` keeps its one designed failure, `byDeps`.
- `tests.sh` checks all examples and the read-back tests against
  `tests.expected`.

**Direct replacement (`migrate.py`).** 160 definitions were rewritten
automatically. The rewriter changes only calls of the direct shape: the
arguments before the split are textually the definition's own, and the
argument at the split is a recursive field. Everything else was left
unchanged for the checker to reject by scope. All 160 rewritten
definitions type-check unchanged.

**Helper cycles (12).** The helper takes the recursive result as a
parameter and is declared first:
- `Arith`: `pcFaceLoN`, `plFaceLoN`, `sfS`, `flS`, `slS`;
- `Sum`: `cl1`, `cctop`;
- `Cat`: `encT-inj-nn`, which takes both results of `node s t`;
- `CSimp`: `top`;
- `CDSurj`: `sucCase`;
- `CLocD`: a new type alias `MissT m n`. `cases` and `fgM` take
  `mi : MissT m n`; `miss`'s branch `suc n'` calls `fgM n' m ih-n' ..`;
  and `fg = fgM n m (miss m n)` comes after `miss`;
- `CBoxHorn`: `max-or` moves its parameter `P` after `j k`, into the
  motive, with one call site changed.

**Reordering only.** 28 definitions were moved before their first use:
`singL`, `skipDg0`, `hxi`, `vc-aux`, `ol-pt`, `la-pt`, `c0s`, `c1s`, `c2s`,
`ccs`, `cnm-f1`, `step`, `bdCase`, `shCase`, `incSh` (twice), `dldl`,
`up2`, `leb-split'`, `sk2`, `hi`, `idcase`, `pw-id`, `g'`, `pwf`, `msT`,
`s'`, and the helpers above.

**Substantive (1): `VLift.lift-refl`.** It is recursion on `x`, with `y` in
the motive, typed by the new alias `LR A f`.
- `lr-fwd` gets the equality `g b = f a` from `sym (r a .. (g b) .. (sym Q))`:
  the swapped recursive call is undone by symmetry.
- A new helper `lr-bwd` uses `r` directly.
- `lift-refl` passes `r` to both helpers.

**The fallback.** It fires 19953 times in the full check, exactly as often
as in `defenv` (counted in a scratch copy). So the migration adds no use of
it: its frequency comes from the existing conversion of splits. It stays
experimental and counted.

**Timing.** The full check takes 54.4 s, the same as `defenv` in the same
session. Maximum resident memory is 789 MB against 709 MB (+11%). No file
changed by more than 0.3 s.

## 11. Review of the trusted changes (19 October 2026)

**Scoping.**
- *Fixed:* a data type was in scope in its own parameters and type, not
  only in its fields (`data D (x : D)` and `data D : D` were type errors,
  not scope errors). Now `resDef'` binds it for the constructor fields only.
- Checked:
  - modules and records can't name themselves inside their bodies;
  - `let`/`where` blocks are sequential, and a `where` local can't see its
    definition;
  - `#fails` blocks follow the same rules.
- *Residual, not a scoping hole:* the checker still enters consecutive
  definitions as one evaluation group (`enterGroup`). The resolver forbids
  referring to a later member, and no value reachable from an earlier
  member's terms contains a later one. So read-back (hole filling) can't
  write a later name either.

**Positivity.** `fieldError` accepts a mention of `D` only as `D ps` or as
`(ys : Ψ) → D ps` with `D` not in `Ψ`, where `ps` must be exactly the
parameters (terms and levels, in order). Every other mention is rejected:
under `Id`, `Σ`, a level or constraint product, a `let`, or as an argument
of another type. It runs on every block, including `#fails`, before
filling.

**Annotation.**
- It is computed from the data definition's fields (`recShape`), which
  positivity certifies, and it is forced on every split by `hasHole`.
- *Fixed:* when filling failed (relevant for files trusted under `--only`),
  every unannotated result was bound to one shared constant, so two of them
  were convertible. Now an unannotated result is a lazy internal error.
- *Pre-existing, not changed:* unfilled holes are likewise one shared
  constant (`_unfilled`), in definitions that failed filling.

**Reduction.**
- `recBind` binds `app f vᵢ`, or a closure over the branch environment with
  the split itself.
- *Fixed:* the binders of the result *type* of a function field now have
  their own prefix (`%z`), separate from those of the value closure (`%y`).
  Before, the separation relied on `eqClos` never comparing a `Pi` closure
  with a lambda closure.

**Quotation.**
- Paths are computed after binders are renamed.
- `canonicalRecs` checks every recursive result on a path against the
  canonical one before a split is written back as its definition applied
  to the path, and refuses otherwise.
- The check unfolds with no locks, since it only verifies a value that
  already exists.

**Pre-existing, noted, not changed:** a branch for a constructor the data
type doesn't have is accepted, and never checked (`checkSplit` walks the
data type's constructors). It can't be reached. `defenv` does the same.

**After the fixes.**
- 3 new `#fails` in `examples/primrec.seg` (56 declarations).
- `tests.sh` is unchanged otherwise.
- Full check: 11816 declarations, 0 failed, 54.4 s, 789 MB; fallback 19953.

## 12. Cleanup before freezing (19 October 2026)

**Unfilled holes** follow the same fail-on-use policy as unannotated
recursive results.
- The filling pass evaluates partly filled terms (to compute the types of
  later arguments), so `eval` keeps a placeholder for `Hole` while it
  works.
- When filling a declaration fails, its unfilled term keeps no `Hole`. The
  remaining holes become `Unfilled` (`unfilledHoles`), whose evaluation is
  an error. This applies to the type of a parameter, a module instance, and
  the type and body of a definition; a `let` passes its failure up to the
  enclosing definition.
- So a hole whose filling failed is never equal to anything, including in
  a run that trusts that declaration.
- A first attempt, an error on every `Hole`, broke 13 definitions of `core`
  through the filling pass's own evaluations. It was replaced by this one.
- Regression: `examples/unfilled.seg` (expected failures, in
  `tests.expected`).

**Unknown constructors.** A branch for a constructor the data type doesn't
have is now an error (`checkSplit`). Regressions: two `#fails` in
`examples/primrec.seg`, one of them on `Empty`.

**Result.** Full check: 11816 declarations, 0 failed, 53.3 s, 789 MB;
fallback 19953. `tests.sh` matches `tests.expected`.

**The implementation is frozen here.** The conversion fallback is left for
a separate investigation. Its justification must cover dependent motives and
the fresh variables for recursive results, not only agreement on closed
constructor values.
