domain/lazy: the lazy evaluator of Henderson and Morris ("A Lazy Evaluator",
POPL 1976), by intersection types -- doc/lazy-intersection.tex in Unit, with
indexed inductive families (doc/INDEXED.md).  No axioms, no Theory
parameter, no postulates, no holes.  Committed locally (df09d63, e6c280a).

The Agda ~/DOMAIN/LAZY was used only for the syntax of Hyper-Pure LISP, the
memory and the rules (Syntax/Heap, Syntax/Step) and for Example 4; its domain
layer (finite elements, stage-stratified order, consistency proof) is
replaced by the types of the note.

CHECK.  ./segc domain/lazy all: 16 modules, 0 failed;
seg All.seg: 823 declarations, 0 failed, 0.10 s.  Max --opened: 30
(Example4.round2: memory lookups); outside Example4, 18 (Step.step-inv).
Agda 2.9.0 on ~/DOMAIN/LAZY (copy in the scratchpad, clean, one run):
2.2 s real, --profile=modules total 2,085 ms (ObsConsistent 806 ms,
OrderProps2 235 ms).  The two developments prove the same theorems by
different arguments, so this is not a like-for-like comparison.

FILES (lines)                       note / Agda
  Lib.seg        147  sums, Booleans as propositions, Nat order, atoms (Agda Domain/Basic)
  Types.seg      414  section 2: types, Le (Def 2.1), Sel/PSel/ASel, Les, Lemma 2.2
  Syntax.seg     146  section 1: cells, memories, upd, Lookup, environments (Agda Syntax/Heap)
  Observe.seg    418  section 3: RuleI, Prem, prem, Obs (Def 3.1), CellQ, transfer, Lemma 3.2
  Gen.seg        333  inversion at cells of known form (generation + Lemma 2.2)
  Rules.seg      308  Theorem 4.1: [C], CDR, [I], [Fa], [A], [E], PLUS, [Fb]
  Closures.seg   200  Theorem 4.1: [G], [L]
  Funarg.seg     262  Theorem 4.1: [Fc]/[Fd] = allocation + rewrite
  Step.seg        82  Step (Agda Syntax/Step + st-F), Theorem 4.1 (step-inv, alloc-inv)
  Eval.seg       322  section 5: Ev (the procedure Eval), Corollary 5.1
  Bound.seg      203  memories bounded by N: N is fresh (bounded-fresh), kept by
                      rewrites below N and allocation at N; list memories
  Example4.seg   128  Example 4 (Agda Example4): the observation alpha : 1
  Example4Run.seg 217 Example 4: the paper's run, example4-halts
  Base.seg, Prelude.seg: symlinks to ../../core.

MAIN STATEMENTS
  Lemma 2.2 (Types):  le-les : (s t : Ty) -> Le s t -> Les s t ;
      les-le : (r k : Ty) -> Les r k -> Le r k ;
      les-trans (r p k : Ty) (x : Les r p) (y : Les p k) : Les r k ;
      inv-at (r : Ty) (a : Atom) (h : Le r (at a)) : Sel r (at a) ;
      inv-atom, inv-pair : Le r (pair a b) -> InvPair r a b,
      inv-arr (beta-soundness) : Le r (arr a b) -> InvArr r a b, where
      InvArr r a b = (f g d t : Ty) * Sel r (arr f g) * ASel r d t * Le a d * Le t b.
  Lemma 3.2(1) (Observe): obs-env (mu) (G D : Env) (p : Nat) (t : Ty)
      (le : EnvLe D G) (h : Obs mu (jdg G p t)) : Obs mu (jdg D p t).
  Lemma 3.2(2) (Observe): cell-ind (generation: a filter containing the
      types given by the rules of mu p contains all the types of p), and
      cell-ind-rec (the same, with the property on the LABEL self-premise).
  Transfer lemma (Observe): obs-transfer (mu nu) (H : Closed mu (Obs nu)) :
      (J : Jdg) -> Obs mu J -> Obs nu J ;  rewrite-inv for a one-cell rewrite.
  Theorem 4.1 (Step):
      step-inv (mu) : (nu : Nat -> Cell) -> Step mu nu -> Inv mu nu,
        Inv mu nu = ((J : Jdg) -> Obs mu J -> Obs nu J) * ((J : Jdg) -> Obs nu J -> Obs mu J);
      alloc-inv (mu) : (nu) -> AllocStep mu nu -> (p : Nat) -> Not (Id Cell (mu p) efree) ->
        (G : Env) (t : Ty) -> (Obs mu (jdg G p t) -> Obs nu (jdg G p t)) * (Obs nu (jdg G p t) -> Obs mu (jdg G p t)).
  Corollary 5.1 (Eval):
      partial-correctness (mu nu) (p) (h : Ev mu p nu) (n : NonFree mu p) : PresAt mu nu p
        (p non-free in nu, same types in mu and nu in every environment);
      ev-value : Ev mu p nu -> Value nu p ;
      eval-atom (mu nu p a) (h : Ev mu p nu) (n) (e : Id Cell (nu p) (equote a)) (G t) :
        (Obs mu (jdg G p t) -> Le (at a) t) * (Le (at a) t -> Obs mu (jdg G p t)) ;
      eval-pair: ends in a CONS => IsPair mu G p (type om x om, no at a / atom / arrow type);
      eval-fun: ends in a closure => IsFun mu G p (type om -> om, no at a / atom / pair type).
  Example 4 (Example4): example4 : Obs mu (jdg gnil zero at1)  (alpha : 1 in the
      initial memory, through two unfoldings of the LABEL, round1/round2);
      example4-atom : Ev mu zero nu -> Id Cell (nu zero) (equote a) -> Id Atom a (num n1);
      example4-not-pair, example4-not-fun.
  Example 4, the run (Example4Run): example4-halts :
      (nu : Nat -> Cell) * (Ev mu zero nu * Id Cell (nu zero) (equote (num n1))).
  Freshness (Bound): bounded-fresh (N mu) : Bounded N mu -> Fresh mu N.

INDEXED FAMILIES
  Le, Sel, PSel, ASel, Les (2-3 indices), Lookup (alist, variable, address),
  RuleI (rule instances, indices cell and type, parameter the environment),
  Obs (parameter the memory, index the judgement; the premises of a rule are
  a FUNCTION FIELD (j : Prem G (mu p) t r) -> Obs mu (prem G p (mu p) t r j),
  which gives the FUNARG rule its one premise per binding without mutual or
  nested families), Step, AllocStep, Allocs, Ren, Ev (3 indices, memories
  as indices).  Recursion through the function field works as documented
  (explicit Pi types for the split).
  Inversions: almost all are done by large elimination on the index,
  NOT by index equations: the motive is a function of the index computed by
  a split on it (Types.LesInv, Closures.ThetaCons, Gen.PairSel/ArrSel OmH,
  MeetH, LeafH, Example4.lookup-cons), so the branch at the constructor's
  target reduces it.  Index equations (INDEXED.md section 6) appear only in
  Observe.cell-ind / obs-copy, where the eliminator of Obs is used at fixed
  (G, p) (motive "Id Env (jG J) G -> Id Nat (jp J) p -> ..").  Rule
  instances are read through CellQ (cell-view / cell-build), one form per
  cell.

CHECKER ISSUE FOUND.  A hidden argument in a branch of a split on a family
with TWO indices, when the branch's target has a non-variable index, fails:
    data Two : (m n : N) -> U a = t-here (m : N) : Two (suc m) m | t-any (m n : N) : Two m n ;
    g3 : (m n : N) -> Two m n -> Empty -> Fin m = split {
      t-here m -> \ h -> efq h ; t-any m n -> \ h -> efq h } ;
    ==> in the branch t-here: no type for %ix2g3 []
(efq {A : U a} (e : Empty) : A.)  With one index it works.  Workaround used:
absurd with the type explicit (Gen.PairSel/ArrSel).  Reproductions:
scratchpad hidbug/Bug2.seg, Bug3.seg.

CORRECTIONS / DEVIATIONS WITH RESPECT TO THE NOTE (now incorporated in the note)
 1. Lemma 2.2(3): stated positively -- "r has an arrow component, and a
    possibly empty selection of arrow components s_i -> t_i has
    s <= /\ s_i and /\ t_i <= t"; the empty selection is the case om <= t,
    with no negative "otherwise".  Pairs likewise (one rule, a pair
    component and a selection).  Selections are multisets (a meet of two
    selections is a selection), which makes the union in transitivity a
    constructor.  Transitivity is by induction on the depth of the middle
    type with meets NOT counted (selections may repeat components, so the
    size of /\ s_i can exceed that of the middle type, the depth cannot).
 2. Lemma 3.2(2) is used as an induction principle (cell-ind); each
    inversion chooses a filter.  For a FUNARG cell the filter "one choice of
    types for th" needs the meet of two choices and Lemma 3.2(1): the step
    the note keeps for [L] backwards is already part of generation, and is
    used for [G] forwards, [Fa], [Fc]/[Fd] backwards and [L] backwards.
 3. The LABEL rule has a premise about its own address.  Hence the copying
    rules ([C], [I], [Fa], nu = mu[mu q / p0]) need, backwards, "every type
    of p0 is a type of q" in mu, to move a LABEL rule from p0 to q; forwards,
    that q and p0 hold the same cell in nu (Observe.obs-copy).
 4. [G] forwards is not "the same steps backwards": it needs the single
    choice s' of funarg-inv, beta-soundness, and the updated choice
    s'[x := s].  Backwards, the choice for th must be s[x := om]: the
    binding of x in th is shadowed by the new binding and has no premise.
 5. [L] backwards needs no induction beyond the transfer lemma: the local
    step meets TWO choices, that of the FUNARG rule of nu p (giving p : s x)
    and the one generation gives for p : s x in mu (s2 at x, s /\ s2
    elsewhere).  The note's "meet of all the types chosen in the
    derivation" is not needed.  [L] forwards is the note's induction, on
    the types of pl in G[th : s], using the inductive hypothesis on the
    LABEL self-premise (cell-ind-rec).
 6. [Fc]/[Fd] need the allocated cells to be free AND to occur in no cell
    of the memory (Funarg.Fresh); otherwise an alist or a component pointing
    at the free cell would see the new content and invariance fails.  In
    the paper this follows from the consistency of the memory; the note's
    "no consistency hypothesis" holds with this freshness condition.  The
    rule is split into allocations (AllocStep; all cells but the allocated
    one keep their types) and a one-cell rewrite (st-F; all cells keep their
    types).  Theorem 4.1's "every cell of mu" = every non-free cell.
 7. The forward directions of [A], [E], [I], PLUS, [Fb] use Lemma 2.2 to
    refute impossible branches (at a <= at b gives a = b; at a is below no
    pair type; a CONS cell has no atom type, via "every type of a CONS cell
    is above a meet of pair types", Gen.cons-shape).
 8. Eval as a relation (Ev): each case rewrites with the rule in the memory
    reached, the redex cells being restated there (the paper's Eval assumes
    them).  In Corollary 5.1 the evaluated cell stays non-free because the
    copies are of evaluated cells (values), so no allocation hits it.  The
    statements hold in every environment, not only the empty one.
 9. Example 4: the observation derivation (as in the Agda) and its
    consequences through Corollary 5.1, and the paper's run
    (Example4Run.example4-run : Ev mu 0 h21, h21 0 = (QUOTE 1) by refl;
    14 allocations, 21 rewrites, ported from the trace of unit-indexed/lazy).
    Each allocation is at the first free address and fresh by
    Bound.bounded-fresh: the initial memory is bounded by 17 (bounded-list),
    each rewrite writes a cell below the bound (bounded-upd), each
    allocation raises it by one (bounded-alloc).
10. Section 8 of the note: the observation relation is one indexed family,
    but the FUNARG premises ("for each binding") need a function field
    indexed by the bindings; rule instances are therefore separated from
    their premises (RuleI, Prem, prem).

NOTE.  The untracked directory unit-indexed/lazy/ (another session, not
touched here) inverts arrows by a "filter interpretation" (a predicate
preserved along the derivation of Le), which avoids the syntax-directed
relation and its transitivity; the present development follows the note
(Les and transitivity) and uses Lemma 2.2 for the inversions.
