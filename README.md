# Unit

**Mathematical attribution: all mathematical results concerning the D
modality and the D_n modalities in this repository are due to Christian
Sattler.** This includes the constructions and proofs, the localisation
results, the finite approximations, their truncation properties, and the
strict-limit and homotopy-limit results for their tower. The corresponding
Unit files and notes record a formalisation and exposition of Christian
Sattler's mathematics.

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

    plus (n : N) : N -> N = split { zero -> n ; suc m | r -> suc r } ;

Here `r` stands for `plus n m`. A definition is not in scope in its own body,
so this is the only form of recursion: primitive recursion at higher types,
as in Hilbert's *On the infinite* (1925) and Gödel's system T.

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
  model at D. All the mathematical results concerning D are due to
  Christian Sattler: D is a strict monad, DA is fibrant when A
  is, the two maps DA → D²A are homotopic homotopy equivalences, and the
  universal property of η.
- [`postnikov-limit.pdf`](doc/postnikov-limit.pdf): Christian Sattler's
  results on D and the D_n modalities. For a type A of the
  poset model, DA is the strict limit of the tower of its finite
  approximations D_N A and, for fibrant A, its homotopy limit (the
  comparison with the internal limit is a homotopy equivalence); the maps of
  the tower need not be fibrations.
- [`sag.pdf`](doc/sag.pdf): what has been formalised of synthetic algebraic
  geometry, and how.
- [`chatelet-descent.pdf`](doc/chatelet-descent.pdf): descent of finite
  freeness and of bases with a retraction, following the checked proof.
- [`finite-projective-flat.pdf`](doc/finite-projective-flat.pdf): the
  constructive finite-matrix proof that finite projective modules are
  exactly the finitely presented flat modules, with a correspondence to
  the formal declarations.
- [`PRIMREC.md`](doc/PRIMREC.md), [`RECORDS.md`](doc/RECORDS.md): design notes
  on recursion through eliminators and on records versus modules.

The `.tex` sources are next to the PDFs.

## The model (`core/`)

`core/All.seg` imports the 245 files in dependency order. Function
extensionality and univalence of the metatheory are the two parameters of one
segment, `Model`; `ModelUA` instantiates the whole development from
univalence alone (function extensionality is derived in `FunExtUA.seg`).
`core/DESIGN.md` maps the files to the sections of the model, and of
`doc/postnikov-limit.pdf` (layer L9b).
All mathematical results in the D and D_n development (layers L9 and L9b,
including its supporting constructions and proofs) are due to Christian
Sattler; this attribution also appears in the individual source files.

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
- `chatelet`: Châtelet's theorem from SAG and sheafification, with descent
  of finite freeness and split bases proved, together with the required
  algebraic and geometric prerequisites; also finite projectivity iff
  finite presentation and flatness over any commutative ring.

## Building and checking

The checker is written in Haskell (GHC; the packages `base`, `containers` and
`directory`). The executable is called `seg`.

    cabal build
    ./run-tests.sh | diff tests.expected -   # the examples in examples/
    ./segc core all                # check the model (about 70 s)
    ./segc core changed            # after an edit: the changed files and their dependents
    ./segc sag/torsor all          # one of the sag/ developments (each under 1 s)
    ./segc sag/chatelet all        # Chatelet, descent, and finite projectivity

`segc` starts a checking server that loads the development once and keeps
the results; `./segc core stop` stops it. Every declaration has a budget of
10 seconds. `tests.expected` records the current output: the failures of
`unfilled.seg` are intended (unfilled hidden arguments must fail on use);
`byDeps` in `locks.seg` fails because instances are no longer identified
through the dependencies of a definition.
