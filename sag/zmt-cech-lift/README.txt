Generic Cech syzygy lifts and family primitives
==============================================

1. Result and ownership

This directory closes two integration gaps between the generic polynomial
kernel construction and the finite zigzag certificate:

  (a) Per-chart homogeneous kernel lifts give an actual finite-support
      shifted Cech-family lift in any natural subset-cardinality.
  (b) Closed families below the top cardinality have actual previous-degree
      primitives; top families whose finite coordinate vector vanishes
      have actual previous-degree primitives too.

There are seven local .seg files, 239 new declarations. Older sources are
relative links to zmt-cech-action and zmt-certificate-general; no shared
source, earlier development, checker or .git was modified. No new axioms,
infinite choices or resizing principles are introduced. Nothing is
committed. All.seg uses precisely the inherited foundational parameters.

The base of these wrappers is any commutative set-ring A. The local-to-
global lift receives HomogeneousKernel.Matrix.Data, the constructed finite
homogeneous kernel data, and homogeneous term-list representatives of its
columns. This directory does NOT separately select these data from CFN;
the certificate agent's construction supplies them under truncation.
Nor does this directory assume the desired local or global Cech lifting
equation: the former is imported as the proved LocalizedSyzygies theorem,
and the latter is constructed here.

2. Index and orientation conventions

Natural exponents are Fin n -> Base.Nat, Laurent exponents Fin n -> Int.
Sub n is the existing recursive finite bitset type. Newest Fin vertex
inr tt is first in the orientation, as in zmt-cech-general.

Integer cardinality topRank(q) corresponds to subset size q. Ordinary
Cech degree is q-1. Rank zero is the augmentation. In particular, the
singleton-coordinate top primitive lands in the augmentation; no claim
of vanishing ordinary H^0 is made. The empty-coordinate development is
augmented, without a projective P^(-1) interpretation.

3. Informal proof corresponding to the declarations

FiniteChartChoice
  choice proves truncated finite dependent choice over Sub n by induction
  on n: choose the Top-indexed entry at n=0; at n+1 combine choices on
  the absent and present halves with map2. select/top name the dependent
  assembling functions. No untruncated choice is claimed.
  Witness records one finite exponent list supporting every coefficient
  family indexed by a given type. sub-union combines explicit single-
  chart supports by concatenating the recursively combined absent and
  present support lists. A coefficient outside the union is outside each
  part, so its chosen component vanishes. finite-sub performs the finite
  choice and leaves the resulting common support truncated.
  fin-union does the corresponding concatenation for a finite family of
  chart-indexed coefficient families. finite-fin uses the existing finite
  Fin-choice theorem before this explicit union. No infinite index set
  is subject to a choice operation.

GlobalCechSyzygies
  ChartSum.val proves that extracting a coefficient from a finite cochain
  sum gives the finite sum of its coefficients, by induction on the sum.
  Input receives the original homogeneous polynomial matrix g, its
  ring-degree proof hg, and its termwise shifted-degree proof gg.
  Chosen receives finite kernel data w, term representatives hp of its
  columns, ring comparison hrep, and their termwise degree proof hh.
  At[k,R] constructs the actual shifted-family matrices G and H using
  ShiftedMatrixAction. Their standard twist vectors are k-d_i, k-c_j and
  k-W.shifts_j. Here R is any integer subset-cardinality.

  Lift[y,hy] starts with the genuine family kernel equality G(y)=0.
  kernel converts that equality to the coefficientwise chart equation,
  using ChartSum and the defining matrix operations. common forms a
  truncated uniform support list for every component of y.
  WithSupport supplies this list, the actual chart vanishing, the
  homogeneous Laurent degrees, and kernel to the proved local chart
  lifting theorem. choices chooses its solutions over the FINITE Sub n.

  Selected constructs each output coefficient from the chosen local
  solution. It is explicitly zeroed when card(s) differs from R. This is
  necessary: a local lift of zero need not itself have been chosen zero.
  supported combines the local finite-support witnesses by finite-sub;
  support passes this support through the cardinality test. van combines
  the proved local degree, chart-support and wrong-rank vanishing laws.
  lifted is consequently an actual cochain family in the target module.

  equation-case uses the local action equation at the correct cardinality.
  At a different cardinality, each lifted component is zero, its action
  is zero by mulP-zero, and y itself is zero by its actual cochain rank
  condition. equation combines ChartSum and coefficient extensionality
  into the genuine module equality H(lifted)=y. Finally the finite choices
  and common support are eliminated only into the truncated Result.

CechRankTransport
  bad transports the cardinality mismatch clause along an integer equality.
  move keeps a cochain's exact raw coefficients and support, transporting
  only that proved vanishing condition. val is its coefficient equation;
  lin packages this as a D-linear map. This named transport isolates the
  predecessor/successor equality used in natural-cardinality primitives.

FamilyPrimitives
  BelowTop[n,a,k,p,ne] concerns cardinality q=suc p. Input extracts the
  componentwise closedness equation from the genuine family equality.
  Each component applies GenericCech.Operations.Primitive with ne and
  closedness, then moves its actual primitive from pred(topRank q) to
  topRank p by CechRankTransport and pred-suc. The family primitive is
  assembled componentwise. equation uses coefficient extensionality and
  the named primitive equation to obtain actual family equality.

  Top[p,a,k] has ambient coordinate number n=suc p. Its input is a family
  of top cochains and a genuine equality of its ShiftedTopPresentation
  coordinate vector to zero. pi-zero applies the constructed finite
  top-zero theorem in every summand. The top decomposition then gives
  d h(y)=y. The same rank transport assembles an actual previous-degree
  family primitive. No outgoing-closedness hypothesis is needed at top.

NaturalCardinality
  top-raise compares the integer cardinality of a finite coordinate set
  with iterated integer successor. lt-ne follows by induction from a
  strict natural inequality: the zero case uses the proved finite
  cardinality bound, and successors cancel with pred-suc. Thus q<n gives
  exactly the integer inequality needed by BelowTop, without a new order
  axiom or a cast supplied by the caller.

PrimitivePackages
  BelowTop.contract inserts the constructed actual primitive and equation
  into the exact truncated Contract type used by FiniteZigzagCertificate.
  Top.top repackages the finite-coordinate extraction into EXACTLY the
  Comb.Free codomain, using the existing extraction linearity laws; the
  pointwise carrier and operations coincide, so no equality of complete
  module records is needed. Top.base combines that map with the actual
  top primitive. Top.terminal transports this entire package along the
  named ambient equality n=suc p, rather than transporting a diagram.

4. Exact public APIs

GlobalCechSyzygies.Over[A,setA,n]
 .Input[a,r,d,c,g,hg,gg]
 .Chosen[w,hp,hrep,hh]
 .At[k,R]
 .Lift[y,hy].lift : Trunc[Result]

Here:
  d : Fin a -> Base.Nat; c : Fin r -> Base.Nat
  g i j : finite natural-exponent term list (input i, output j)
  hg i j : Hom(d_i-c_j)(phi(g_ij)) in the constructed polynomial tower
  gg i j : HomShift(c_j,d_i,g_ij)
  w : HomogeneousKernel.Matrix.Data
  hp j i : term list representing kernel column j at input i
  hrep j i : phi(hp_ji)=w.columns(j,i)
  hh j i : HomShift(d_i,w.shifts_j,hp_ji)
  k,R : arbitrary integers
  y : G.Source.El, an ACTUAL shifted cochain family at cardinality R
  hy : Id G.Target.El (G.lin.f y) G.Target.mod.mz
  Result = (z : H.Source.El) * Id H.Target.El (H.lin.f z) y

The original g is neither replaced nor homogenised here. Its entries are
transposed only to match the row/column convention of ShiftedMatrixAction.
The named G/H family modules are exported by At.

FamilyPrimitives.Over[D,setD]
 .BelowTop[n,a,k,p,ne]
 .Input[y,closed]
   primitive : Target.El  -- cardinality p
   equation  : Id Source.El (Back.lin.f primitive) y
  where Source has cardinality suc p, closed is the genuine outgoing
  family differential equation, and
  ne : Not(Id Int (topRank n) (topRank(suc p))).

FamilyPrimitives.Over[D,setD]
 .Top[p,a,k]
 .Input[y,hz]
   primitive : Target.El  -- cardinality p, ambient n=suc p
   equation  : Id Source.El (Back.lin.f primitive) y
  where Source is the top family and
  hz : Id Coords.free.M (Coords.lin.f y) Coords.free.mz.

NaturalCardinality.lt-ne q n lt
  : Not(Id Int (topRank n) (topRank q))
NaturalCardinality.Over[D,setD,n,a,k,p,lt].P
  instantiates BelowTop directly when lt : NatOrder.Lt (suc p) n.

PrimitivePackages.Over[D,setD]
 .BelowTop[n,a,k,p,ne].contract
  : exact truncated Contract interface on the natural-cardinality families.
 .Top[p,a,k].terminal n e
  : Top[p,a,k].Ambient[n].Terminal, for e : Id Nat n (suc p).
  Terminal is EXACTLY
    (v : Nat) * ((top : Lin[D,Source.mod,Comb.Free[D,v].mod]) *
      ((y : Source.El) -> top(y)=0 ->
        Trunc[(h : Previous.El) * d(h)=y])).
  Source has ambient coordinate number n and cardinality suc p;
  Previous has ambient coordinate number n and cardinality p.

All equations above are actual module equalities, not merely raw
coefficient statements. Internal raw equations are converted by the
existing coefficient extensionality theorem.

5. Checks, audits and regressions

Commands from unit:
  timeout 55 ./segc sag/zmt-cech-lift all
From sag/zmt-cech-lift with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt-cech-lift.opens

Recorded results:
  segc: 158 modules, 0 failed.
  Fresh All.seg: 8696 declarations, 0 failed, about 4.3 s.
  239 new local declarations, in seven files.
  --opened: at most 31 definitions opened, at most 0.02 s per declaration.
  --opens: all 239 local profiles report "nothing else opened".

The opening profiles explicitly include the finite recursion, support
unions, rank tests and conditions described above. At the matrix/kernel
and final equality bridges they also include raw/submodule/product
carrier, accessor and operation aliases, finite sum, polynomial action
and matrix-entry definitions. No quotient representative or local
syzygy proof is unfolded to prove a new lifting equation.

FamilyPrimitiveRegression instantiates below-top primitives in the two
middle degrees of four coordinates, the four-coordinate top primitive,
the singleton top-to-augmentation primitive, and empty-coordinate
below-top exactness. Relevant action, top-enumeration, n=0/n=1/n=4 and
sign regressions of the prior directories remain imported and checked.

A deliberate mutation replacing the wrong-cardinality zero output by
the ring unit was rejected by choose-zero, wrong-rank and equation-case.
It was restored, and the complete fresh checks pass again.

6. Remaining integration

The certificate agent still supplies the constructed finite homogeneous
kernel chain, its homogeneous term representatives and consecutive-matrix
identities, then instantiates these actual family lifts/primitives into
its proved finite zigzag certificate. This directory does not claim full
ZMT, Rees comparison, arbitrary-base descent or arbitrary-dimensional
weighted dependence. No polynomial-linearity of the selected contraction
is used or asserted.
