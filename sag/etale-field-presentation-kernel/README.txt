Original presentation equations generate the kernel of a generated cover
======================================================================

1. Checked theorem

PresentationKernel.Over[R,setR].At[
  Q,S,p,ps,q,u,generator-map,hom-ext]

Inputs:
  R    : any commutative set-ring;
  Q,S  : R-algebras;
  p    : Presentations.Presentation;
  ps   : Presentations.Presents p S (the ordinary universal property);
  q    : Fin p.1 -> Q;
  u    : R-algebra map Q -> S;
  generator-map i : u(q_i)=ps.1.1(i);
  hom-ext : for every R-algebra T and maps f,h:Q->T, agreement on
            the q_i implies pointwise agreement on every element of Q.

Outputs:
  number = length p.2;
  generators j = eval_Q(q, original presentation equation j);
  killed j : u(generators j)=0;
  kernel a (h:u(a)=0) : merely coefficients c_j in Q with
                       a = sum_j generators(j)*c_j;
  ideal-kernel a : membership in that generated ideal implies u(a)=0.

The kernel signature is exactly the one accepted by
  etale-field-basis/FiniteFreeQuotientBasis.Over[R,setR,dec].At
and uses FiniteIdeal.Sums[Q.ring].lin number generators c.
No finite-freeness, field, reducedness, or surjectivity hypothesis is needed
for the kernel theorem itself. A finite free cover and its surjectivity are
used only when the caller subsequently constructs a finite basis of S.

2. Proof

FiniteGeneratedIdeal forms the ideal of the original equations, with
membership defined by a truncated finite coefficient witness. It proves
the ideal laws and gives a witness for each generator.

PresentationKernel constructs the actual quotient algebra Q/J by reusing
QuotientRing. The images of q_i satisfy the original equations. The given
presentation of S therefore supplies a map S -> Q/J. Its composite with u
agrees with the quotient projection on q_i, hence on all of Q by hom-ext.
If u(a)=0, the class of a is zero in Q/J. Quotient effectiveness gives the
required J-membership witness. The reverse direction follows because every
original equation is killed by u.

There is no global representative choice, no additional presentation
existence assumption, and no supplied kernel-generation principle. All
truncations are eliminated into propositions.

3. Files and dependencies

  FiniteGeneratedIdeal.seg       17 new declarations
  PresentationKernel.seg        43 new declarations
  PresentationKernelRegression.seg 24 new declarations
  All.seg
  presentation-kernel.opens

The imported algebra/quotient files are unchanged relative links. The
canonical presentation-construction files are imported only for regressions.
No shared/checker file was changed, no new axioms were introduced, and
nothing is committed. All.seg uses the same univalence, replacement, and
surjection parameters as the existing developments.

4. Validation

  ./segc sag/etale-field-presentation-kernel all
    48 modules, 0 failed, 0.20 s summed declaration checking time.

  Fresh built seg on All.seg with --opened:
    1432 declarations, 0 failed, 0.27 s;
    all 84 new declarations <=0.01 s, at most 18 definitions opened.

  --opens sag/etale-field-presentation-kernel/presentation-kernel.opens
    all 84 new declarations covered; every one says "nothing else opened";
    fresh full run 0 failed, 0.28 s.

Regression instances over any commutative set-ring R:
  - no generators and no equations: R -> R has the zero kernel;
  - no generators and the single equation 1=0: R -> R/(1), with the
    target constructed by PresentationExistence, has the whole kernel.
The second explicitly computes the original kernel generator as 1.
Changing that generator to 0 was rejected by the checker, then restored
and rechecked.

Audit logs are in /tmp/etale-field-presentation-kernel-{opened,opens,all}.log.
Some comparisons unfold the existing quotient-ring operation aliases; those
are explicitly included in the .opens budgets. No abstraction beyond what
those budgets show is claimed.
