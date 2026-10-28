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

    plus (n : N) : N -> N = split { zero -> n ; suc m | r -> suc r } ;

Here `r` stands for `plus n m`. A definition is not in scope in its own body,
so this is the only form of recursion: primitive recursion at higher types,
as in Hilbert's *On the infinite* (1925) and Gödel's system T.

This repository contains the checker and six developments written with it:

- a formalisation of a model of univalent type theory over a base category
  with an interval, with finite posets and simplicial sets as instances
  (`core/`);
- formalisations of results of *A foundation for synthetic algebraic
  geometry* (Cherubini, Coquand, Hutzler) over univalence and Rijke's
  axiom of replacement (`sag/`);
- formalisations of *A foundation for synthetic Stone duality* and
  *Cohomology in synthetic Stone duality* (Cherubini, Coquand, Geerligs,
  Moeneclaey), up to Theorem 5.16 and Theorem 3.3.2 (`sag/stone`,
  `sag/stoneseq`, `sag/cca`, `sag/em`, `sag/ccacoh`);
- a formalisation of *Constructive finite free resolutions* (Coquand,
  Quitté), §2–§8, with the true grade and Wiebe's theorem of *An
  elementary proof of Wiebe's theorem* (Coquand, Tête) (`sag/cffr`,
  `sag/koszul`, `sag/wiebe`);
- a constructive theory of Girard's dilators: normal form, well-foundedness
  up to the Howard ordinal, morphisms, connected components and kinds
  (`dilators/`).
- π₃(S²) = ℤ and π₄(S³) = ℤ/2 in univalent type theory, each from the
  universal property of the sphere alone, by a Postnikov universal property
  (`sag/pi3-s2-postnikov`).

**Mathematical attribution: all mathematical results concerning the D
modality and the D_n modalities in this repository are due to Christian
Sattler.** This includes the constructions and proofs, the localisation
results, the finite approximations, their truncation properties, and the
strict-limit and homotopy-limit results for their tower. The corresponding
Unit files and notes record a formalisation and exposition of Christian
Sattler's mathematics.

**Mathematical attribution for `sag/pi3-s2-postnikov` (π₃(S²) = ℤ and
π₄(S³) = ℤ/2): David Wärn developed the universal-property strategy used
here, together with the delooping and cup-product constructions.** Our
contribution was to develop the argument in detail and formalise it in Unit.
Owen Milner formulated the Sính invariant in homotopy type theory.

## Documents (`doc/`)

- [`unit.pdf`](doc/unit.pdf): Unit, its uniform treatment of definitions
  and what checking the developments below opens.
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
- [`chatelet.pdf`](doc/chatelet.pdf): Châtelet's theorem (a Severi–Brauer
  variety with a point is projective space) as checked in `sag/chatelet`,
  with the changes made to the source note and a correspondence with the
  formal declarations.
- [`chatelet-descent.pdf`](doc/chatelet-descent.pdf): descent of finite
  freeness and of bases with a retraction, following the checked proof.
- [`finite-projective-flat.pdf`](doc/finite-projective-flat.pdf): the
  constructive finite-matrix proof that finite projective modules are
  exactly the finitely presented flat modules, with a correspondence to
  the formal declarations.
- [`horrocks-divisor.pdf`](doc/horrocks-divisor.pdf): a new constructive
  proof of rank-one Horrocks over a local ring, by division. An ideal of
  A[X] containing a monic polynomial, with an A-linear retraction, is
  generated by a monic polynomial. Induction on the degree of a monic
  element, with the retraction fixed; Nakayama without determinants and
  without the radical; no residue field, no freeness, no Schanuel. With the
  correspondence to `sag/horrocks`.
- [`horrocks-determinant.pdf`](doc/horrocks-determinant.pdf): a short
  proof of the same theorem by determinants (A[X]/L is free, the
  characteristic polynomial of X lies in L), checked with the determinant
  of `sag/exterior`.
- [`horrocks-gluing.pdf`](doc/horrocks-gluing.pdf): rank-one Horrocks over
  any commutative ring, by a local-global principle for comaximal monoids,
  organised as the formal proof suggested.
- [`wiebe.pdf`](doc/wiebe.pdf): Wiebe's theorem relative to an ideal J
  (Δ⊥ = (a) and (a)⊥ = (Δ) modulo (J, b) when Gr(b) ≥ n), following
  Coquand–Tête with the generic change as a chain of elementary operations,
  as checked in `sag/wiebe`.
- [`dilators-constructive.pdf`](doc/dilators-constructive.pdf): a
  constructive theory of dilators (Girard, *Proof Theory and Logical
  Complexity*, chapters 8 and 9), as checked in `dilators/`.
- [`pi4-s3.pdf`](doc/pi4-s3.pdf): π₄(S³) = ℤ/2 by a Postnikov universal
  property: the main ideas of the formal proof (strategy due to David Wärn;
  Owen Milner formulated the Sính invariant in homotopy type theory). The detailed notes:
  [`br-universal.pdf`](doc/br-universal.pdf) (the marked universal property
  of BR), [`cross-term.pdf`](doc/cross-term.pdf) (R deloops),
  [`cup-square.pdf`](doc/cup-square.pdf), [`h4.pdf`](doc/h4.pdf),
  [`fibre-h3.pdf`](doc/fibre-h3.pdf),
  [`circle-torsors.pdf`](doc/circle-torsors.pdf),
  [`mapping-fib.pdf`](doc/mapping-fib.pdf),
  [`postnikov-presentation.pdf`](doc/postnikov-presentation.pdf),
  [`finite-truncation.pdf`](doc/finite-truncation.pdf), and
  [`pi3-s2-postnikov.pdf`](doc/pi3-s2-postnikov.pdf) for π₃(S²) = ℤ.
- [`pi3-s2.pdf`](doc/pi3-s2.pdf): π₃(S²) = ℤ by a Postnikov universal
  property: the main ideas of the formal proof, in the same form as
  `pi4-s3.pdf`.
- [`PRIMREC.md`](doc/PRIMREC.md), [`RECORDS.md`](doc/RECORDS.md): design notes
  on recursion through eliminators and on records versus modules.

The `.tex` sources are next to the PDFs.

## The model (`core/`)

`core/All.seg` imports the files in dependency order. Function
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
- `affine`, `tensor`: Section 3 (the affine axioms, Proposition 3.3.4,
  tensor products, pullbacks, boundedness).
- `closed`, `opens`: Sections 4.1 and 4.2 (closed and open subtypes).
- `schemes`, `gluing`: Section 5 (schemes; gluing, Section 5.3).
- `cokernel7`, `qc-schemes`, `bridge7`: Section 7.1 (kernels and
  cokernels of weakly quasi-coherent modules, schemes) and Theorem 7.3.6.
- `pn`, `laurent`, `picard`: projective space P^n; line bundles on P^n are
  Line × Z (Theorem 7.3), Aut(P^n) = PGL_{n+1}; the Picard group of P^1.
- `horrocks`: rank-one affine Horrocks over any commutative ring, with
  two proofs of the local case: by division (`DivisorStep`) and by
  determinants (`DeterminantHorrocks`); see the three Horrocks notes in
  `doc/`.
- `exterior`: the exterior algebra Λ(Aⁿ) by its universal property, and
  the determinant defined from it: det(AB) = det A det B, adj(A) A =
  det A · I, the characteristic polynomial (monic of degree n), the
  determinant trick, integrality, Cayley–Hamilton; exterior coordinates,
  duality, contraction, det Aᵀ = det A and the Plücker–Sylvester relation
  of *Preuve conceptuelle d'une relation de Plücker–Sylvester* (pcc2)
  (`exterior/DESIGN.md`).
- `chatelet`: Châtelet's theorem from SAG and sheafification, with descent
  of finite freeness and split bases proved, together with the required
  algebraic and geometric prerequisites; also finite projectivity iff
  finite presentation and flatness over any commutative ring.

## Finite free resolutions and grade (`sag/cffr`, `sag/koszul`, `sag/wiebe`)

Coquand–Quitté, *Constructive finite free resolutions*, with the true
grade of Coquand–Tête, in the same setting as `sag/`; no prime ideals, no
decidable equality, true grade relative to a finitely generated ideal J.
Each directory has a `README.md` mapping statements to declarations.

- `cffr`: §2 (regularity, the local–global Lemma 2.3, McCoy's Theorems
  2.4–2.5 with minors as exterior coordinates), Theorem 3.1 (McCoy for
  polynomials), Lemma 4.3, Theorem 6.8 (ranks and grades along a
  resolution), Corollaries 7.5 and 7.6, and §8: Lemmas 8.1–8.6, Theorem
  8.7 (the Cayley determinant is a gcd), Corollary 8.8 (Hilbert–Burch),
  Theorem 8.9 and Corollary 8.10.
- `koszul`: complexes and long exact sequences, the Koszul complex and the
  Koszul grade (Lemmas 6.1–6.5, Theorem 6.4), the true grade (ctete §1:
  Lemmas 1–7, Theorem 9; cffr Proposition 6.6, Lemma 6.7, localisation),
  true grade ⇒ Koszul grade, Vasconcelos (Theorem 2.6, Corollary 2.7),
  Theorems 7.1–7.3 (Peskine–Szpiro) and Corollary 7.4 (Rees).
- `wiebe`: Wiebe's theorem (ctete Theorem 11, Corollary 12) relative to J;
  see `doc/wiebe.pdf`.

## Homotopy groups of spheres (`sag/pi3-s2-postnikov`)

In the setting of `sag/em` (univalence and replacement as parameters; function
extensionality, truncations and Eilenberg–MacLane spaces derived). The sphere
is not a parameter of the development: the universal property of S² (resp.
S³) is the parameter telescope of a module. Two theorems are checked:

- `Presentation.Final.pi3-S2 : GIso[pi3 S2 base, ab-grp Zab]`, π₃(S²) = ℤ
  from the S² axiom;
- `Pi4Sphere.Pi4S3[S3, base, surf, ump3].pi4-S3 : GIso[pi4 S3 base, ab-grp Z2ab]`,
  π₄(S³) = ℤ/2 from the S³ axiom (π₄X is π₃(ΩX) by definition).

The candidate Postnikov stage is BR, the delooping of the fibre R of the cup
square reduced mod 2; a marked class s : [S³, BR]_* is shown to have the
universal property s* : [BR, Y]_* ≅ [S³, Y]_* for BR and for ‖S³‖₄, which
gives π₄(S³) ≅ π₄(BR) ≅ π₃(R) ≅ ℤ/2. Check with
`./segc sag/pi3-s2-postnikov all`; `README.txt` there maps files to the
notes, and the `.opens` files record, declaration by declaration, the
definitions the checker unfolds. See [`pi3-s2.pdf`](doc/pi3-s2.pdf) and [`pi4-s3.pdf`](doc/pi4-s3.pdf).

## Synthetic Stone duality (`sag/stone`, `sag/stoneseq`, `sag/cca`, `sag/em`, `sag/ccacoh`)

Formalisations of two papers of Cherubini, Coquand, Geerligs and
Moeneclaey, in the same setting as `sag/` (univalence and replacement as
parameters, the axioms of Stone duality as hypotheses), with the
directories placed beside the SAG ones.

*A Foundation for Synthetic Stone Duality*:

- `stone`: countably presented Boolean algebras and their spectra, the
  axioms, open and closed propositions, Stone spaces (Lemmas 3.1, 3.2,
  Corollary 3.7, Theorem 3.11 and its corollaries), compact Hausdorff
  spaces and Theorem 4.18 (closed equality) (`stone/DESIGN.md`).
- `stoneseq`: sequential colimits and limits, overtly discrete types
  (Lemmas 2.3–2.7), countable and dependent choice, Lemmas 5.5–5.10,
  Corollary 5.11 and Theorem 5.16 (H¹(X, Z) = 0 iff Ȟ¹(X, S, Z) = 0, and
  Ȟ¹(X, S, Z) ≅ ‖X → BZ‖₀) (`stoneseq/README.md`).

*Cohomology in Synthetic Stone Duality*, with Eilenberg–MacLane spaces
after Wärn:

- `em` (plain HoTT): K(A, n) for all n, deloopings of maps, fibre sequences
  and their long exact sequences, non-abelian H¹ and Appendix A, the Čech
  groups and Appendix B (Lemmas B.0.5–B.0.7 in the degrees used;
  B.0.7, cited but not in the paper, supplied).
- `cca`: Scott continuity for Stone and compact Hausdorff spaces
  (§2.1–2.4), the interval as a quotient of 2^N, Lemma 3.4.1, Theorem 3.4.3
  (Hⁿ(I, A) = 0 for n ≥ 1), Lemma 3.4.4, the ordered Čech complex and
  Lemma C.0.6.
- `ccacoh`: §3.1, §3.2 (Hⁿ(S, A) = 0 for S Stone) and Theorem 3.3.2 as
  stated: Hⁿ(X, B) ≅ Ȟⁿ(X, S, B) as groups, naturally in B
  (`ccacoh/Thm332A`).

Not formalised: the real numbers and Brouwer's fixed-point theorem
(Foundation §4.4, §5.4–5.5), and Proposition 3.4.5 of the second paper
(it needs n-truncations of arbitrary types). Design, gaps of the papers and
the statements shared between directories: `stone/DESIGN.md`, the
`HANDOFF-*` files, `STONE-INTERFACE.md`, `CCA-DESIGN.md`,
`CCA-INTERFACE.md`.

## Conversion, and what checking opens

Conversion is uniform. Two values are first compared by their names:
strictly, or as the same definition at convertible arguments, without
unfolding anything. Otherwise definitions are opened one at a time at the
head: when both heads are blocked by definitions, the one declared later is
opened (by sequential scope it is the only one whose unfolding can reach the
other), and strict equality is tried after each step. Writing back an
omitted argument as a term recognises the names in scope without computing.
There is no other choice of what to unfold, so the cost of a check reflects
the structure of the proof. A record's constructor `mkM`, generated as
`mkM params fields = new M[params, fields]`, is notation for `new`: applied
to its arguments it is an element at once, and it is never opened.

    seg File.seg --opened          # per declaration: comparisons settled by names,
                                   # by arguments, by components; definitions opened
    seg File.seg --opens F         # F has lines  name: d1 d2 ..  (the definitions
                                   # the informal proof cites); reports the others

`examples/frege.seg` with `examples/frege.opens` is a small example: Frege's
first lemmas on the transitive closure of a relation.

## Building and checking

The checker is written in Haskell (GHC; the packages `base`, `containers` and
`directory`). The executable is called `seg`.

    cabal build
    ./run-tests.sh | diff tests.expected -   # the examples in examples/
    ./segc core all                # check the model (about 50 s)
    ./segc core changed            # after an edit: the changed files and their dependents
    ./segc sag/torsor all          # one of the sag/ developments (each under 10 s)
    ./segc sag/chatelet all        # Chatelet, descent, and finite projectivity

`segc` starts a checking server that loads the development once and keeps
the results; `./segc core stop` stops it. Every declaration has a budget of
10 seconds. `tests.expected` records the current output: the failures of
`unfilled.seg` are intended (unfilled hidden arguments must fail on use);
`byDeps` in `locks.seg` fails because instances are no longer identified
through the dependencies of a definition.
