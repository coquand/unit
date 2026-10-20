# Unit

**Unit** is a small proof checker for a dependent type theory with
definitions. Its module system is based on the segments of Automath: a
module is a list of declarations (units), its parameters are the
declarations without a body, and an instance only binds the parameters,
without copying the body. Besides modules there are record types, types of
tuples with named fields. A record type is written like a module, but it is
a type, and a module is not.

Recursion is only through the eliminators of data types. A function out of
a data type is defined by cases on the constructors; in the case of a
constructor with arguments of the type being defined, the values of the
function on these arguments are available as extra variables:

    plus : N -> N -> N = split { zero -> \ n -> n ; suc m | r -> \ n -> suc (r n) } ;

Here `r` stands for `plus m`. A definition is not in scope in its own body,
so this is the only form of recursion: primitive recursion at higher types,
as in Gödel's system T.

This repository contains the checker and two developments written with it:

- a formalisation of a model of univalent type theory over a base category
  with an interval, with finite posets and simplicial sets as instances
  (`core/`);
- formalisations of results of *A foundation for synthetic algebraic
  geometry* (Cherubini, Coquand, Hutzler) over univalence and Rijke's
  axiom of replacement (`sag/`).

## Documents (`doc/`)

- [`prototype.pdf`](doc/prototype.pdf): the checker: its type theory
  (Π, Σ, records, data types with recursion through eliminators, identity
  type, cumulative universes with level expressions and constraints) and its
  module system.
- [`model.pdf`](doc/model.pdf): the model: relative contractibility
  structures, fibrations, gluing (Theorem 7), univalence, the fibrancy of the
  universe, the instances (posets, constructive; simplicial sets, with
  excluded middle at one point), and identity types with a strict
  computation rule.
- [`localisation.pdf`](doc/localisation.pdf): the localisation of the poset
  model at Sattler's operation D: D is a strict monad, DA is fibrant when A
  is, the two maps DA → D²A are homotopic homotopy equivalences, and the
  universal property of η.
- [`sag.pdf`](doc/sag.pdf): what has been formalised of synthetic algebraic
  geometry, and how.
- [`PRIMREC.md`](doc/PRIMREC.md), [`RECORDS.md`](doc/RECORDS.md): design notes
  on recursion through eliminators and on records versus modules.

The `.tex` sources are next to the PDFs.

## The model (`core/`)

`core/All.seg` imports the 205 files in dependency order. Function
extensionality and univalence of the metatheory are the two parameters of one
segment, `Model`; `ModelUA` instantiates the whole development from
univalence alone (function extensionality is derived in `FunExtUA.seg`).
`core/DESIGN.md` maps the files to the sections of the model.

## Synthetic algebraic geometry (`sag/`)

Each directory has an `All.seg` whose segment takes univalence and
replacement (images and their surjectivity) as parameters; function
extensionality, propositional truncation and set quotients are derived. The
axioms of synthetic algebraic geometry (Loc, SQC) enter as hypotheses where
used. Each directory has a `README.txt`.

- `replacement`: replacement, truncation, univalent completion.
- `sag`, `sag-uniform`: Lemma 2.2.4 (algebraic closure up to double
  negation), from Loc and uniform SQC.
- `bounded`, `presentations`: finitely presented algebras by presentations
  and a universal property, uniform SQC, Proposition 2.2.2, Theorem 3.3.3
  (functions Spec A → ℕ are bounded), the algebra of Example 6.1.9.
- `polynomial`, `projective`: A[X] with its universal property; the
  projective line, Example 6.1.9 and Lemma 6.2.1.
- `torsor`: Lemma 7.4.2 (cocycles and torsors), Theorem 7.4.7 (2-cocycles
  and gerbes), Theorem 7.4.8 (Čech H² of a 2-acyclic finite cover is H², as
  abelian groups, natural under refinement).

## Building and checking

The checker is written in Haskell (GHC; the packages `base`, `containers` and
`directory`). The executable is called `seg`.

    cabal build
    ./run-tests.sh | diff tests.expected -   # the examples in examples/
    ./segc core all                # check the model (about 55 s)
    ./segc core changed            # after an edit: the changed files and their dependents
    ./segc sag/torsor all          # one of the sag/ developments (each under 1 s)

`segc` starts a checking server that loads the development once and keeps
the results; `./segc core stop` stops it. Every declaration has a budget of
10 seconds. `tests.expected` records the current output: the failures of
`unfilled.seg` are intended (unfilled hidden arguments must fail on use);
`byDeps` in `locks.seg` fails because instances are no longer identified
through the dependencies of a definition.
