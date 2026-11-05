domain/mltt-proj: Coquand and Huber's finitary projections ("An adequacy
theorem for dependent type theory", section 3; paper1 section 2.3) on the
filters of domain/mltt.  domain/mltt (owned by another session) is
imported READ-ONLY through symlinks; nothing there is edited.  No
parameters, no postulates.  Not committed.

CHECK.  seg All.seg: 1374 declarations (with domain/mltt), 0 failed, 0.22 s.

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

Infinite.seg (~300 lines): Coquand-Huber section 4, Definition 1 and
Propositions 2-3, on domain/mltt's relation at compact witnesses (RelC,
step 4; uncommitted there at the time of writing).
  Def1[n, D]   TyF X T T' = TyR c T T' for all c in X; TmF V T M M' the
               same at u in V (no type witness, so no "exists a0");
               tyf-prin/tmf-prin: at prin c it is TyR c / TmR c (by M);
               ArgF A V A0 P P' (V consistent, of type A, D |- P = P' : A0,
               TmF V A0 P P'); FamF, AppF: the three conclusions
  FamAt[G, anti].at V   G(V) = union of G x, x in V
  Prop2[n, D, A, G, anti]: prop2-to, prop2-from (A a filter of types):
               TyF (Pi A G) T T' iff PiF T T' (reducts, conversions,
               TyF A A0 A1, family clause at every argument filter V)
  Prop3[n, D, A, G, T, A0, B0, rT, W, M, M']: prop3-to, prop3-from
               (W of type Pi A G): TmF W T M M' iff FunF (applications at
               every argument filter V, in appF W V)
  The right sides quantify over filters, so they are in U l+.

EtaU.seg (45 lines): the paper's example after Corollary 4 (El (N -> N)
= continuous functions El N -> El N) with U in place of N.  UU = Pi U
(x |-> U) is a type (UU-type); for W consistent, EtaU[W, cW]:
  eta       p UU W = lam U (x |-> p U (W x))   (ProjLam at A = G x = U)
  fix-to, fix-from   HasTy W UU iff W = lam U (x |-> p U (W x)).
