Escardo's DialogueTreesHeight (github.com/martinescardo/DialogueTreesHeight)
in Unit: the height of the dialogue tree of every term of System T of type
(N -> N) -> N is below epsilon_0, and epsilon_0 is the least such bound.
With TypeTopology's effectful forcing (EffectfulForcing.MFPSAndVariations:
CombinatoryT, Dialogue, MFPS-XXIX) and Brouwer codes.

Theory parameter: function extensionality only.  No new axioms, no
postulates.

The four theorems (Theorems.seg, Agda Main):
  restated (e) (h : Has e FT) : Le (Sb (height (tree e h))) (Lb tower)
      -- height < eps0, for every typed term (Omega allowed)
  attained (n) : OmegaFree (towerTerm n) * Le (tower n) (height (tree (towerTerm n) ..))
  cofinal (a) (p : a < eps0) : a term of T whose tree has height >= a
  least (b) (phi : every term of T has height <= b) : Le (Lb tower) b
plus no-tower-bound: no level of the tower bounds every term of T.

Architecture (differs from the Agda; see DESIGN.md):
  one generic fundamental lemma for logical relations between models of
  System T (SystemT.seg: record Model, Eval, record Rel, Fund), and four
  models with three relations:
     PM  --LR-->  DM  --HR-->  MajM  --DR-->  TupM
  pointwise   dialogue    majorants     graded tuples < eps0
  LR (Models): correctness of the dialogue interpretation (Escardo's
  main-lemma); HR (Majorant): height (tree t) <= mu t; DR (Bound, with the
  clauses of Predicate and Clauses): mu t <= tsum (tuple t) < eps0.  The
  Agda proves these by three separate inductions on terms.
  Typed terms: untyped terms with Has e t (Unit has no indexed families);
  terms of T are those with OmegaFree e.  The order on Brouwer codes is
  defined by recursion (Agda: an inductive family).

Files (dependency order), with the Agda modules they translate:
  SystemT Dialogue Models          CombinatoryT, Dialogue, MFPS-XXIX (TypeTopology)
  Brouwer Height                   BrouwerCodes, Order, Constructive
  Ordinals Epsilon0 MultClosure    Multiplication, Epsilon0, MultClosure
  Majorant                         Majorant, MajorantAll
  Affine Moves Tuples Cascade Rect MultAffine, Absorb, Move, MoveTuple, Cascade,
                                   CascadeLevel, Rect, RectAdd
  RectAlgebra RectApply RectCurry RectOrbit
                                   RectAlgebra, RectSum, RectApply, RectCurry, RectOrbitAct
  Predicate Clauses Bound          Predicate, SClause, IterClause, Fundamental
  Examples Lower Bracket Sharpness Theorems
                                   (pilot examples), Examples, Sharpness, Main
Article.lagda (the paper index) is not translated.

Check (from unit/):   ./segc sag/dialogue all
  2026-11-05: 31 modules, 0 failed; standalone `seg All.seg` 0.34 s,
  972 declarations, 3624 lines (31 files, plus 4 linked core files).
For comparison, Agda 2.9.0 (TypeTopology ee4e4c86), from scratch: 34.3 s
(242 modules, mostly the TypeTopology library); the repository's own 29
modules 3.0 s once TypeTopology is compiled.  Agda source: 28 modules,
5,643 lines (2,985 code lines), plus the TypeTopology modules used.
