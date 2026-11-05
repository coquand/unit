domain/mltt-proj: Coquand and Huber's finitary projections ("An adequacy
theorem for dependent type theory", section 3; paper1 section 2.3) on the
filters of domain/mltt.  domain/mltt (owned by another session) is
imported READ-ONLY through symlinks; nothing there is edited.  No
parameters, no postulates.  Not committed.

CHECK.  seg All.seg: 711 declarations (with domain/mltt), 0 failed, 0.09 s.

Proj.seg (156 lines)
  Meets P f      f is a meet of elements satisfying P
  projF B X      p B X: the types above a meet of elements of X typed at
                 types of B; a filter with no hypothesis
  proj-sub       p B X <= X
  proj-idem      p B (p B X) = p B X
  proj-mono      monotone in B and X
  enl-proj       Enl X B t gives t in p B X
  Collapse[B, X, ConsF X, TyU B]:
    proj-enl     every element of p B X is above ONE typed element of X,
                 typed at a type of B in U (tp-join, tp-up)
    hasTy-fix    HasTy X B iff X = p B X: El B = fixed points of p B
  proj-univ      p U U = U

ProjPi.seg (136 lines): Coquand-Huber Prop. 1, product at the universe.
  PiClause[A, G, anti, ConsF A, gc].eq :
    FEq (p U (piF A G)) (piF (p U A) (x |-> p U (G x)))
  (<=) generation of a U-typed element of piF A G (asel-cod: the codomains
  of om -> U are above U; ent-vals: typed entries with their values;
  selection lemma Entries.sel); (>=) Sound.sound-pi at p U A, p U o G.

ProjLam.seg (99 lines): Coquand-Huber Prop. 1, function clause
(generalised eta).
  lam-app-sub : lam A (x |-> app W (prin x)) <= W, for every W
  LamClause[A, G, anti, W].sub1 (G antitone only) and
  LamClause[..].Back[TyU A, TyU (G x), gc, ConsF W].eq :
    FEq (p (piF A G) W) (lamF A (x |-> p (G x) (app W (prin x))))
  (>=) by Sound.sound-lam and lam-app-sub.

Hypotheses are those the semantics of terms satisfies (Sem.fam-anti,
sem-cons, soundness).

ProjBot.seg (35 lines): LamU[A, G].eq : FEq (p U (lamF A G)) (prin om),
the clause "p U b = bot otherwise" for functions (no hypotheses).

Not done: the paper's eta example (needs a base type; MLTT_eta has none).
Next: Coquand-Huber Def. 1, Props 2-3, once domain/mltt step 4 exists.
