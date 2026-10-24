SAG Section 5.3: gluing schemes
===============================

Worker B's development. Check from the repository root:
  ./segc sag/gluing all
Independent check:  (cd sag/gluing && "$(cabal list-bin exe:seg)" All.seg)

Dependencies are read-only symlinks: worker A's schemes/ (SmallAffine,
SchemeMaps, Schemes) and, through them, Sections 2-4 and
projective/Quotient.seg.  Foundation: univalence and replacement.
Loc, SQC and Z-choice come as SAGAxioms[l,l].Assumptions, and only
OpenEmbedding and GlueScheme use them (through 4.2.9).

GluePushout.seg: the pushout, no axioms
  Glue[X,Y,V,sX,sY,f,g,ef,eg] for embeddings f : V -> X, g : V -> Y into
  sets.  P = Quot (X + Y) by rel, where
    rel (inl x) (inr y) = Both x y = (w : Fiber f x) * (g w.1 = y)
  and rel on two points of X (or of Y) is equality.  It is
  propositional because f is an embedding; transitivity uses that f and g
  are injective.
  il, ir, glue v : il (f v) = ir (g v); il-embedding, ir-embedding;
  meets : il x = ir y -> Both x y; set.
  pushout B sB : isEquiv (P -> B) (Cocone B) (restrict B) for every set B
  (maps out of P = pairs of maps agreeing on V).  This is the pushout
  for maps into sets only; the universal property against arbitrary
  types is not proved.

OpenEmbedding.seg: composition (Loc, SQC, Z-choice)
  OpenImage A X f = every fibre image is open.
  Compose[...]: an open embedding into an open embedding into a set is an
  open embedding.  The image of h . e at c is "c in the image of h, and
  the point over c in the image of e", open by 4.2.9(a) (Transitivity.sigma).

GlueScheme.seg: 5.3.1 (Loc, SQC, Z-choice)
  Gluing[X,Y,V,schX,schY,f,g,ef,eg,of,og].scheme : Scheme P, for schemes
  X, Y and embeddings f, g with open images.
  il-open: the image of X in P is open, by induction on representatives:
  on X it is everything, on Y it is the image of g.  ir-open likewise.
  Lift: a chart of X (or Y) composed with il (ir) is a chart of P.
  Covers: the n charts of X and the m charts of Y, concatenated
  (FinSum.cases), cover P.
  As in the paper, no chart is intersected with U: the charts of X are
  charts of P because X is open in P.

GluingExamples.seg
  Disjoint[X,Y].sum: X + Y (gluing along Empty) is a scheme; apart: its
  two parts do not meet.  Negative test: il x = ir y is not provable by refl.
