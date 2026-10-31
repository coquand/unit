Constructed base change and preservation of formal unramifiedness
===============================================================

1. Checked result

For any ring map rho:R->K between commutative set-rings, an R-algebra S
with a finite presentation p, and formal unramifiedness Unique_R(S), the
development constructs a K-algebra T with:
  - the finite presentation obtained by mapping every coefficient of p;
  - formal unramifiedness Unique_K(T);
  - an actual R-algebra map S -> restrict(T);
  - for every K-algebra B, an equivalence
      Hom_K(T,B) ~= Hom_R(S,restrict(B)),
    whose forward map is restriction followed by precomposition with that
    inclusion. Thus this is genuine scalar extension by its mapping-out
    universal property.

No field, flatness, injectivity, reducedness, or ZMT assumption is used.
In particular rho may kill nonzero nilpotents. The formal unramifiedness
theorem also works for any other T supplied with the same mapped presentation.

2. Exact interfaces

MappedPresentation.Over[R,K,setR,setK,rho]:
  restrict B                    the R-algebra underlying a K-algebra B;
  restrict-map A B f            its action on algebra maps;
  expression V e                replace each constant r by rho(r);
  equations V es                the mapped list of equations;
  presentation p                the mapped finite presentation;
  value V B x e                 mapped evaluation = restricted evaluation;
  solution-equivalence p B       equivalence between the two solution types.

Its module At[S,p,ps,T,pt] takes
  ps : Presents_R p S,
  pt : Presents_K (presentation p) T,
and exports:
  inclusion : Hom_R S (restrict T);
  inclusion-generators i : inclusion(ps.1.1 i)=pt.1.1 i;
  To[B].forward, backward;
  To[B].backward-generators;
  To[B].fb, bf, universal, equivalence.

Constructed[S,p,ps] uses the actual PresentationExistence construction over K.
It exports algebra, presents, finite-presentation, and BC=At for this model.
No abstract existence principle or tensor-product postulate is supplied.

UnramifiedBaseChange.Over[R,K,setR,setK,rho]:
  At[S,p,ps,T,pt,unique].theorem : Unique_K T,
  where unique : Unique_R S.

  Constructed[S,p,ps,unique] exports:
    algebra             the actual mapped-presentation algebra;
    finite-presentation : FP_K algebra;
    unramified          : Unique_K algebra.

The finite presentation ps is explicit input. If a caller has merely FP(S),
the caller can perform this construction inside that truncation and target
an appropriately truncated existence statement. This directory does not
choose a presentation from a truncated FP hypothesis.

3. Proof of uniqueness

For a K-algebra B and a square-zero ideal N, restrict B to R and reuse the
same ideal, propositional membership, and square-zero proof. Given maps
f,g:T->B with equal reductions modulo N, their composites S->B have equal
reductions over R. Apply Unique_R(S), then injectivity of the mapping-out
equivalence gives f=g.

The quotient rings in both reductions have exactly the same carrier and
operations. The proof compares their underlying quotient classes directly;
it does not identify the R-algebra structure records obtained by different
associations of scalar-map composition. Thus no unjustified transport across
different presentations or quotient constructions is used.

4. Files, checks, and regressions

  MappedPresentation.seg          51 new declarations
  UnramifiedBaseChange.seg        48 new declarations
  BaseChangeRegression.seg        50 new declarations
  All.seg
  etale-field-basechange.opens

Checks:
  ./segc sag/etale-field-basechange all
    51 modules, 0 failed, 0.21 s summed declaration checking time.
  Fresh built seg on All.seg with --opened:
    1583 declarations, 0 failed, 0.29 s;
    all 149 new declarations <=0.01 s, at most 21 definitions opened.
  --opens sag/etale-field-basechange/etale-field-basechange.opens
    all 149 new declarations covered; each says "nothing else opened";
    fresh complete run 0 failed, 0.31 s.

Regressions:
  - the empty presentation over arbitrary rho:R->K;
  - R with the one-generator presentation X=a, with a genuinely constructed
    universal property, then the actual mapped-presentation algebra;
  - rho:Z/4 -> (Z/4)/(2), with the quotient actually constructed;
  - a=2: the mapped constant and the target generator's evaluated value
    are zero, although the source coefficient is the nonzero nilpotent 2.
The last evaluation map comes from the mapping-out equivalence.
Changing that coefficient from 2 to 1 was rejected, then restored and checked.

Audit logs are under /tmp/etale-field-basechange-{opened,opens,all}.log.
Some checks unfold algebra and quotient-ring record aliases; those are
included explicitly in the .opens budgets.

5. Boundaries

This proves preservation of finite presentation and formal unramifiedness,
and constructs the base change by universal property. It does not identify
the model with a chosen tensor product or a chosen quotient special fibre.
It does not construct prime ideals, residue fields, or the denominator
clearing needed by the downstream local theorem.

All dependencies are unchanged relative links. No shared or checker files
were edited, no new axioms were added, and nothing is committed. All.seg has
the same univalence, replacement, and surjection parameters as the existing
developments. The checking server is stopped after validation.
