# Indexed inductive families in Unit — design note

Branch `indexed-families` (worktree `/Users/coquand/CANONICITY/unit-indexed`).
Status: implemented (5 November 2026), see §10.

## 1. Aim

Add indexed inductive families, as in Coquand and Paulin-Mohring,
*Inductively defined types* (COLOG-88, LNCS 417, 1990), and Dybjer,
*Inductive families* (Formal Aspects of Computing 6, 1994), keeping Unit's
discipline: recursion only through the eliminators, written as `split`
with recursive results; no unification, no pattern matching on `refl`,
no mutual or nested types. Motivation: syntax indexed by scope, typing
judgements, reduction relations (the developments in `~/DOMAIN`: LAZY,
MIN, BCDE4), which today must be encoded as untyped data plus a
recursive typing predicate (as in `sag/dialogue/SystemT.seg`).

## 2. Syntax

The annotation of a data type may be a telescope ending in a universe;
its binders are the **indices**. Each constructor then states its
**target**, `D` applied to the parameters and to index expressions:

    data Fin : (n : Nat) -> U =
        fz (m : Nat) : Fin (suc m)
      | fs (m : Nat) (i : Fin m) : Fin (suc m) ;

    data Vec (A : U l) : (n : Nat) -> U l =
        vnil : Vec A zero
      | vcons (m : Nat) (x : A) (xs : Vec A m) : Vec A (suc m) ;

    data Le : (m n : Nat) -> U =
        lz (n : Nat) : Le zero n
      | ls (m n : Nat) (h : Le m n) : Le (suc m) (suc n) ;

A data type without indices is written exactly as today (no target).

Rules (checked by the resolver and `Term.positivityReport`):

- the parameters are uniform: every occurrence of `D` (in a target or a
  field) is applied to exactly the parameter variables, in order;
- index expressions (in targets and fields) do not mention `D`;
- a field mentions `D` only as `D ps es` or `(ys : Psi) -> D ps es`
  (`es` arbitrary index expressions, possibly using `ys`), with `D` not
  in `Psi` — strict positivity as today, with free indices;
- the constructor telescopes and targets are in the scope of the
  parameters, **not** of the index binders of the annotation (those only
  name the indices in the type).

## 3. Representation

The data definition stays "lambdas, then a sum": parameter lambdas, then
index lambdas, then the sum. The sum records, per constructor, its
target index expressions:

    Sum Id Int [(Name, Tel, [Exp])]        -- k = number of indices

and the value `VSum` keeps its environment (parameters and index values
of the instance at hand). `D ps is` is the reference applied to the
parameters and the indices, unfolded by `force` as today.

## 4. Typing

**Formation.** The body after the parameter lambdas is checked against
the annotation, a Π over the indices ending in `U l`; the sum is checked
at `U l` with each constructor telescope in the parameters' scope, and
each target expression against the corresponding index type
(instantiated with the earlier target expressions).

**Constructors (checked, not inferred, as today).** To check `c as`
against `D ps is`: check the arguments against the telescope of `c`
(evaluated with `ps`), evaluate the target expressions with `ps, as`,
and require them to be **convertible** with `is`. No unification:
`fz m : Fin n` checks only if `n` is convertible with `suc m`.

**Split.** A split on an indexed family is the body of a definition of
type

    (i1 : I1) .. (ik : Ik) -> (x : D ps i1 .. ik) -> P i1 .. ik x

where the domain of `x` is `D` applied to the parameters and to **the k
variables just bound, in order** (checked when the split is typed; a
type with a non-variable index is rejected: write the general
eliminator and an equation, see §6). The split absorbs the k index
arguments. The branch for `c xs` is checked against

    P es[ps, xs] (c xs)          -- es the target of c

and a recursive result for the field `x_j : D ps es_j` has type
`P es_j x_j`; for a field `x_j : (ys : Psi) -> D ps es_j(ys)` it has type
`(ys : Psi) -> P es_j(ys) (x_j ys)`. For k = 0 all of this reduces to
the present rules.

## 5. Evaluation, conversion, read-back

- A split on a family with k indices has arity k + 1: `app` accumulates
  the k index values, then dispatches on the constructor of the last
  argument (the indices are not inspected). `whnfC`, `blockingRef`,
  `unfold1` look at argument k + 1 as the scrutinee.
- Recursive results: `recBind` applies the split to the field's index
  values (the evaluated index expressions of the field type) and to the
  field; `recLam` likewise under the binders `ys`. The annotation
  (`fillC.annotate`, `recShape`) records the field's index expressions.
- Conversion and strict equality are unchanged: sums and splits by
  identity and dynamic part, constructors by name and arguments.
- Read-back (`byPath`, `canonicalRecs`, `quoteTest`): the path of a
  split now passes k index arguments before the constructor.

## 6. What the user writes instead of dependent pattern matching

Matching at a fixed index (Agda's `f : Fin zero -> Empty`, or the
inversion of `HeadRed1 (App f a) N`) has no direct form. It is written
as a split at general indices with an equation on the index:

    no-fin0-gen : (n : Nat) -> (i : Fin n) -> Id Nat n zero -> Empty = split {
      fz m -> \ e -> zero-suc m (sym e) ;
      fs m i -> \ e -> zero-suc m (sym e) } ;
    no-fin0 (i : Fin zero) : Empty = no-fin0-gen zero i (refl zero) ;

Inversion lemmas follow the same pattern, with `idJ`/`subst` to transport
along the index equations. This is more verbose than Agda but stays
within eliminators, without K.

## 7. Places to change (from the map of `src/`)

- `SegParse.hs`: `data` annotation and constructor targets (`units`,
  `labels`, `RData`), `resDef'` RData (scopes of targets/indices),
  traversals of `Sum` (`numE`, `binderUnits`, `shadowReport`, `expUses`,
  `mapExp`, `splitReport`, `pathE`).
- `Term.hs`: `dataParams`/`fieldError`: parameters uniform, indices free
  and `D`-free; check targets.
- `Seg.hs`: `Sum` with targets; `checkW` for Sum, Con, Split;
  `checkSplit`/`checkSplitAll`/`recCx`/`recTyExp`; `fillC` (Con, Split,
  `fillBranch`, `annotate`), `recShape`; `app`, `recBind`, `recLam`,
  `whnfC`, `blockingRef`, `unfold1`; `byPath`, `canonicalRecs`,
  `quoteTest`; traversals `unfilledHoles`, `hasHole`, `freeNamesE`;
  messages mentioning `d ps`.
- Docs: `prototype.tex` (labelled sums, small sums, definitional
  equality, evaluation, checking; the remarks saying "no indexed
  inductive families"), `PRIMREC.md`.

Estimated: about 20 functions, a few hundred lines.

## 8. Tests and validation

- `examples/indexed.seg`: Fin, Vec, Le; `vhead : Vec A (suc n) -> A`
  through the general eliminator; `#fails` for: a constructor at the
  wrong index; a non-uniform parameter; `D` in an index expression; a
  split whose type has a non-variable index; a branch at the wrong type.
- Regression: `./run-tests.sh | diff tests.expected -` unchanged except
  for the new file; `./segc core all` and several `sag/` developments
  unchanged in declarations and failures (no indexed family anywhere,
  k = 0 path).
- A soundness check: the eliminator computes (`#conv`), and the known
  attacks (index confusion `fz : Fin zero`, K via index equations) fail.

## 9. First uses

1. `~/DOMAIN/LAZY` (Henderson's lazy evaluator, 5,522 Agda lines):
   heaps, `Step`, `AlistLookup`, the observation relation.
2. `~/DOMAIN/MIN` (subject reduction and Π-injectivity, 25,105 lines).
3. `~/DOMAIN/BCDE4` (Π-injectivity for the BCDE system, the theory Unit
   implements).

## 10. Implementation (5 November 2026)

Implemented as designed, uncommitted on branch `indexed-families`.

**Syntax.** `data D (ps) : (i1 : I1) .. (ik : Ik) -> U l = c (tel) : D ps es | ..`
(also `I1 -> .. -> U l`). The indices are the leading products of the
annotation; a constructor of a family must have a target, a constructor of
a data type without indices must not.

**Representation.** `Sum Id Tel [(Name, Tel, [Exp])]`: the index telescope
(the names bound by the index lambdas of the body, after the parameter
lambdas; an anonymous index is named `%ixN`) and per constructor its fields
and target indices. `Split Id Int bs`: the number k of indices absorbed;
`-1` means "to be decided by the filling pass". `RecR j n es y`: the filling
pass records the field's indices `es` as terms of the branch (pattern
variables, and for a function field its binders `recArg`), obtained by
evaluating the field's indices and quoting them back. Values:
`VSum t dyn ix cs env`, `VSplit t dyn k absorbed bs env`.

**Resolver (`SegParse`).** `labels` parses targets; `resDef'` (RData) peels
the indices from the resolved annotation, resolves each target in the scope
of the parameters and fields (not of the index binders) and checks it is
`D ps es` with exactly the parameters and k indices (`targetIdx`). A split
gets k = 0 unless the program has an indexed family and one of its labels
(or the split has no branch) is a label of one (`ixLabels`); then k = -1.
Traversals of `Sum`/`Split` updated (`numE`, `pathE`, `splitReport`,
`shadowReport`, `binderE`, `expUses`, `nameSplit`).

**Positivity (`Term`).** `dataParams` drops the k index lambdas;
`fieldError` accepts `D ps es` with k `D`-free indices; targets must not
mention `D`.

**Checker (`Seg`).**
- Formation: `checkTargets` checks each target against its index type,
  instantiated with the earlier targets (dependent index telescopes).
- Constructors: `checkConIndices`, conversion of the target with the
  expected indices, no unification.
- Split: `splitIndices` decides k from the type and the labels (a split on
  a data type without indices whose labels are exactly its constructors is
  as before); `peelIndexed` finds the first binder whose type is a family
  having the labels, and requires it to be binder k + 1, at the k variables
  just bound, in order, with parameters that do not depend on them (checked
  by peeling a second time at fresh indices and comparing the parameters).
  `checkSplitI` checks branches at `P es (c xs)` (`motiveAt`, sequential
  application of the type); `recCxI` gives the recursive results their types
  and checks that the indices recorded by the filling pass are convertible
  with those of the field (`recIdxAgree`), so evaluation cannot be fed wrong
  indices. The index variables are unnamed fresh variables (`freshIdx`), so
  no quoted term can mention them.
- Fill: `fillC` decides k with the same function and writes it;
  `fillSplitI` annotates positions and indices of recursive fields;
  `fillTargets` fills holes in targets; `dataShape` stays lazy.
- Evaluation: `app` absorbs k indices, then dispatches; `recVal` applies
  the split with no index absorbed (`splitBase`) to the field's indices and
  the field; `whnfC`, `blockingRef`, `unfold1` treat an unsaturated split
  as a function (`saturated`). The absorbed indices are bound in the branch
  (`bindIdx`, names `recIdx`) so that `byPath` can write back a split nested
  in a branch; `eqVal`/`conv'` compare absorbed indices; `rb` prints them.
- Read-back: `byPath`/`canonicalRecs` pass the k indices before the
  constructor (`branchIdx`); `quoteTest` works on indexed splits.

**Deviations.** (1) The design's "the indices are not inspected" holds;
in addition the fill pass must see every possibly-indexed split (k = -1 is a
hole), which is why the resolver approximates by labels. (2) For a
recursive *function* field of an indexed family the type of the split must
be written as explicit products (the motive is read off the closure body,
`motiveLam`); otherwise a clear error. (3) The split type must start with
exactly the k index binders (`\ p -> split` for an extra argument before
them). (4) Messages: a split on a family at non-variable indices or with
index-dependent parameters has its own message; everything else for data
types without indices is unchanged.

**Validation.** `examples/indexed.seg`: 76 declarations, 0 failed (Fin, Vec,
Le, a family with a function field, Eq with J, dependent indices, a family
in a module; `vhead` and `no-fin0` through the general eliminator with an
index equation; `#conv` of each eliminator; `#fails` for index confusion
(`fz zero : Fin zero`, `vnil : Vec N one`), targets at the wrong index or
type, non-uniform parameters, `D` in an index, splits at non-variable or
permuted indices, wrong branch types, K at a fixed index and K with an
index-dependent parameter). `run-tests.sh` gained a `--quote-test vsum`.
Regression against the checker built from HEAD: all other examples give
identical output; `core` 282 modules, 0 failed, per-module counts identical;
sag/freegroup 1240, dialogue 957, searchable 234, jutting 94, torsor 1590
declarations, 0 failed, output identical.

### Index names (fix after independent testing)

An independent test session found that index binders, kept by name
around the sum in the core, captured visible names: with
`one : N = suc zero`, `data B1 : (one : N) -> U a = b1 : B1 one` was read
as `b1 : B1 n` for every `n` (no ⊥, since checking and evaluation agreed
on the captured reading, but contrary to §2).  Fixed in the resolver
(`resDef'`, RData), as for module heads and constructor fields: an index
may not be named like a visible definition, the data type or a parameter,
and the index names are distinct.  A field may reuse an index name (it is
bound inside the constructor; resolver and evaluation agree), as in `Le`.
Regressions: the `#fails` blocks at the end of `examples/indexed.seg`.

**Absorbed indices are not read-back names (fix found by the LAZY
formalisation).**  In a branch, the indices the split absorbed are bound
internally (`%ix1`, `%ix2`, ...) to the values of the constructor's target.
When such an index is a bare constructor variable, as `m` in
`t-here (m : N) : Two (suc m) m`, the internal name was bound to the same
generic as `m`, and the read-back (used to write a solved hidden argument
back as a term) could choose `%ix2` as the name of `m`, which is not in scope:
"no type for %ix2".  The read-back scope now ignores the internal index
bindings.  This is a scoping fix; hidden arguments are still solved by
one-way matching only, and the elaboration has no unification.
Regression: `two-elim` in `examples/indexed.seg`.
