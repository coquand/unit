# The versions of the checker (2026-11-13)

The checker is `src/` + `app/` of this repository.  Several branches carry
different versions of it; this note says which is which.

## The current checker: branch `typed-split-env`

Worktree `/Users/coquand/CANONICITY/unit-checker`.  It contains every
experiment below that was kept, then:

- the environment is a list of static declarations and the values of its
  variables (`Env = [Decl] + [Val]`, plus a cache);
- `Decl` is the one notion of declaration: `[x : A]`, `[x : A = e]`, data,
  split (nested splits too), module, record (head and body), instance,
  level, constraint; a program is a list of `Item`s (a declaration, or the
  two commands: lock strategy, directive);
- abstraction is typed, every bound variable is declared with its type;
- a split is a declaration evaluated as in mTT10 (every definition is
  recursive; recursive results are definitions); no internal binders;
- a segment is found by one lookup (`envMods`).

Checked: `run-tests.sh`; `~/DOMAIN/UNIT` (`UNIT/check.py`: 12187 + 4909
declarations, 0 failed); `sag/` freegroup, stone, exterior, dialogue,
horrocks, pn, chatelet, categories (0 failed).  Not yet checked: `core/`
(through `segc`), the other `sag/` directories.

## Its ancestors, all contained in it

| branch | what it added |
|---|---|
| `indexed-families` | indexed inductive families, split as eliminator; `domain/` developments |
| `exp-shape-count` = `exp-decl-bodies` | data types and splits as declarations, DataDecl |
| `exp-record-eta` | eta for records in conversion; fixed fields are values |
| `exp-typed-neutrals` | neutral values carry their type; lambdas carry their domain |

## Not contained in it

| branch | what it is |
|---|---|
| `core-abstraction` | the main line of the developments (577 commits of `.seg` work); its checker is the one before `indexed-families`, plus a change to `app/Main.hs` |
| `main` | `core-abstraction`'s older state plus one note (`doc/unit1`) |
| `exp-id-family` | 4 experiments after `exp-typed-neutrals`: the identity type as an indexed family (`core/Identity.seg`), refilling an inferred argument that misfits its domain |

## Which development uses which checker

- `~/DOMAIN/UNIT` records the checker of `indexed-families` by path and
  hash (`/Users/coquand/CANONICITY/unit-indexed`, commit 78832185).
- The developments of this repository (`core/`, `sag/`, ...) are checked
  with `core-abstraction`'s checker (worktree `/Users/coquand/CANONICITY/unit`).

## To do

Bring the developments of `core-abstraction` and the current checker
together on one line, check everything with it, then retire the other
branches.
