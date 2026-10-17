# Unit

**Unit** is a small proof checker for a dependent type theory with
definitions, whose module system is based on the segments of Automath: a
module is a list of declarations (units), its parameters are the
declarations without a body, and an instance only binds the parameters,
without copying the body. Segments also serve as record types.

This repository contains the checker and a formalisation, written with it, of
a model of univalent type theory over a base category with an interval, with
finite posets and simplicial sets as instances.

## Documents (`doc/`)

- [`prototype.pdf`](doc/prototype.pdf): the checker: its type theory
  (Π, Σ, records, labelled sums, identity type, cumulative universes with
  level expressions and constraints) and its module system.
- [`model.pdf`](doc/model.pdf): the model: relative contractibility
  structures, fibrations, gluing (Theorem 7), univalence, the fibrancy of the
  universe, the instances (posets, constructive; simplicial sets, with
  excluded middle at one point), and identity types with a strict
  computation rule.
- [`localisation.pdf`](doc/localisation.pdf): the localisation of the poset
  model at Sattler's operation D: D is a strict monad, DA is fibrant when A
  is, the two maps DA → D²A are homotopic homotopy equivalences, and the
  universal property of η.

The `.tex` sources are next to the PDFs; each document ends with a table
relating its statements to the files of `core/`.

## The formalisation (`core/`)

`core/All.seg` imports the 205 files in dependency order. Function
extensionality and univalence of the metatheory are the two parameters of one
segment, `Model`; `ModelUA` instantiates the whole development from
univalence alone (function extensionality is derived in `FunExtUA.seg`).
`core/DESIGN.md` maps the files to the sections of the model.

## Building and checking

The checker is written in Haskell (GHC; the packages `base`, `containers` and `directory`). The
executable is still called `seg`.

    cabal build
    ./run-tests.sh                 # the examples in examples/
    ./segc core all                # check the whole formalisation (about 30 s)
    ./segc core changed            # after an edit: the changed files and their dependents

`segc` starts a checking server that loads the development once and keeps
the results; `./segc core stop` stops it. Every declaration has a budget of
10 seconds, and every file of `core/` checks in under 2 seconds.
