Generic finite-coordinate Laurent/Cech contraction
================================================

1. Checked result and scope

This directory proves the finite-coordinate Cech contraction uniformly in
the number n of homogeneous coordinates. The base is ANY commutative
set-ring D. Neither a field nor coherence/CFN is required here.

There are ten new .seg files and 384 new declarations. Every imported
older .seg file is a relative symbolic link to ../zmt-lifting. No shared
library, earlier development, checker, or other agent's directory was
modified. All.seg inherits precisely the existing foundational parameters
of zmt-lifting/All.seg; there are no new axioms or choice assumptions.

The construction is structural in n, not a family of sign tables. It
provides actual modules of finitely supported Laurent coefficient families,
linear maps d, h and pi, d^2=0, the homotopy d h+h d+pi=id, pi d=0,
primitives outside top subset-cardinality, and d h+pi=id at top cardinality.

2. Indices, degrees, and the augmentation

GenericLaurent.Exp n = Presentations.Fin n -> ZInt.Int.
For n+1 coordinates, head is the value at inr tt, tail restricts to inl.
The projective Laurent degree total is head + total(tail). These are the
same Fin constructors used by sag/zmt-syzygies-general/FiniteExponents.seg;
that independent track uses natural rather than integer entries.

GenericCube.Sub 0 = Top and Sub(n+1) = Flag * Sub(n), with flags absent
and present. These are finite bitsets, including the empty subset. The
new vertex inr tt is FIRST in the orientation; recursively the remaining
vertices have the old orientation. A fixed orientation, rather than a
comparison operation on arbitrary Fin terms, determines all signs.

The module Cochains[n,k,r] consists of finite coefficient families c(s,m)
that vanish unless:
  - total(m)=k (projective twist);
  - every coordinate with negative exponent belongs to s (chart support);
  - card(s)=r (integer subset-cardinality).
Vanishing outside these conditions is stated using Not(Id ...), and does
not require decidable equality of D or a choice of representatives.
Finite support is a truncated list of exponent vectors outside which all
components vanish. The operations keep the same support list; addition
uses its concatenation. Only elimination into propositions is needed.

Ordinary Cech degree q corresponds to r=q+1, for r>=1. Rank r=0 is the
augmentation, the polynomial chart on the empty subset. Thus the general
primitive theorem includes augmented exactness in rank 1; this must NOT be
read as vanishing of ordinary H^0. For ordinary positive intermediate
cohomology use 2<=r<n. No numerical inequality is a theorem hypothesis:
the stronger primitive theorem merely needs r != topRank(n).

For n=0 this is a one-term augmented complex, d=h=0 and pi=id.
It is not asserted to model a projective space P^(-1). For n=1 the top
ordinary chart is rank 1 and the rank-0 term is still the augmentation.
GenericRegression checks both edge cases explicitly.

3. Informal proof and its formal declarations

GenericCube:
Write a raw subset family on n+1 vertices as (a,b), according as the new
vertex is absent or present. Define d(a,b)=(d a,a-d b), starting with
d=0 on n=0. The lemmas d-left and d-right state these equations by refl.
Induction proves d-cong, d-add and d-sm. The associated linear map dlin
gives d-zero, d-neg and d-sub. Then
  d^2(a,b)=(d^2 a, d a-d(a-d b))=(0,0),
which is exactly dd, using the named d-sub and induction hypothesis.

GenericContraction:
A mask records the negative coordinates of a monomial. If its newest
coordinate is nonnegative, choose that vertex and put h(a,b)=(b,0),
pi(a,b)=0. If it is negative, put h(a,b)=(h a,-h b) and
pi(a,b)=(pi a,pi b). At n=0 take h=0, pi=id.
The map therefore chooses the first nonnegative vertex, or no vertex
when all coordinates are negative. The congruence and linearity lemmas
follow by the same recursion. Included names the terms needed to check
the second component without repeatedly spelling their definitions.
The declaration htpy proves d h+h d+pi=id by the two sign cases.
It holds even for raw families before chart support is imposed.

GenericSupport:
bad(mask,s) means that s omits a negative vertex; missing(s) means that
s is a proper subset. full-or-missing supplies the constructive dichotomy.
Van is vanishing at bad subsets. The lemmas d-van and h-van follow the
same two flag cases as d and h: removing a vertex cannot repair an omitted
negative vertex, and inserting the chosen nonnegative vertex is allowed.
p-local states that pi(c)(s) depends only on c(s). This gives p-zero-at,
p-van, and p-missing: on supported families pi is zero at every proper
subset. all-d-zero/all-h-zero preserve a coefficient family of zeros.

GenericDegree:
card counts present flags as an integer. Rank means vanishing at unequal
cardinality. Restriction to the absent component keeps rank k; restriction
to the present component has rank pred(k). The lemmas d-rank, h-rank,
p-rank prove their respective changes +1,-1,0. Integer predecessor and
successor avoid exceptional cases at zero or negative rank. PiZero uses
p-missing on proper subsets and rank at the full subset; therefore pi=0
if rank differs from topRank(n). Primitive combines this with htpy and
closedness to give d h(c)=c, together with support and rank of h(c).

GenericLaurent:
Chart builds the submodule of coefficient families with truncated finite
support and a specified vanishing condition. supp-zero/add/neg/sm give
the finite-support operations, cond-* add the vanishing condition, and
eq is coefficient extensionality for the resulting module.

GenericCech:
Bad combines projective degree, chart support, and subset-cardinality.
Cochains extracts each exponent fibre and its three vanishing laws.
Operations applies d, h, pi to that fibre. dSupp/hSupp/pSupp preserve the
original finite-support list. dVan/hVan/pVan combine the previously
proved support/rank laws and preservation of a zero projective fibre.
The resulting d,h,p are actual elements of their target modules.
SquareZero.dd lifts raw dd. Operations.Primitive lifts the raw primitive
theorem without choice and gives a genuine finite Laurent primitive.

GenericTop:
choice proves pi is either identity or zero, depending only on the signs.
This gives p-d, p-add and p-sm. TopOnly means vanishing at proper subsets;
d-top proves a family concentrated at the full subset has outgoing d=0.
Since p-top says pi(c) is TopOnly, pd-zero follows from p-d and d-top.
decomposition proves d h(c)+pi(c)=c for a closed c; top-decomposition
supplies its closedness from TopOnly.

GenericCardinality:
bound proves card(s) != suc(raise j(topRank n)) for every j, by induction
on n; it is the strengthened finite-cardinality bound needed for the
absent flag. proper then proves a proper subset has cardinality unequal
to the full subset. rank-top converts top Rank into TopOnly.

GenericCechTheorems:
Linear packages d,h,p as IdealPowers.Lin maps using their named raw
linearity lemmas and coefficient extensionality. Homotopy lifts htpy,
pi d=0 and the top-only image of pi. Top uses rank-top and d-top to show
top cochains are closed, and lifts the top decomposition.

4. Main API (after module Over[D,setD])

GenericCech.Over[D,setD].Cochains[n,k,r].mod
  The actual D-module, with El, val, fibre, support, rank, projective.

GenericCech.Over[D,setD].Operations[n,k,r]
  d : Cochains[n,k,r].El -> Cochains[n,k,sucZ r].El
  h : Cochains[n,k,r].El -> Cochains[n,k,predZ r].El
  p : Cochains[n,k,r].El -> Cochains[n,k,r].El
  Closed c : (s,m) -> dRaw(c)(s,m)=0

GenericCech.Over[D,setD].Operations[n,k,r].Primitive[c,ne,closed]
  ne : Not(Id Int (topRank n) r)
  primitive : Cochains[n,k,predZ r].El
  equation(s,m) : d(primitive)(s,m)=c(s,m)

GenericCech.Over[D,setD].SquareZero[n,k,r].dd c
  The outgoing differential of d(c) is zero.

GenericCechTheorems.Over[D,setD].Linear[n,k,r].{d,h,p}
  The three corresponding IdealPowers.Lin maps.

GenericCechTheorems.Over[D,setD].Homotopy[n,k,r]
  equation c s m             : d h(c)+h d(c)+pi(c)=c
  projection-boundary c s m  : pi(d(c))=0
  projection-top c s m proper: pi(c)(s,m)=0 on proper subsets

GenericCechTheorems.Over[D,setD].Top[n,k]
  closed c                  : d(c)=0, for c of rank topRank n
  decomposition c s m       : d h(c)+pi(c)=c

These identities are coefficientwise to avoid transporting the codomain
along sucZ(predZ r)=r or predZ(sucZ r)=r. Their inputs and outputs are
actual module elements, and Chart.eq gives coefficient extensionality.

5. Regressions and validation

GenericRegression checks the empty-coordinate augmented complex, the
one-vertex contraction for positive and negative signs, and the formulas
  d(c)_01 = c_1-c_0,
  d(c)_012 = (c_12-c_02)+c_01,
  d(c)_0123 = ((c_123-c_023)+c_013)-c_012.
The latter two are exactly the characterising Cech4.d1/d2 formulas,
with labels taken in our fixed orientation. They use existing Cech4
abelian-group lemmas, not the old contraction or sign tables.
P2, P3Degree1, P3Degree2 instantiate the actual primitive theorem at
n=3/r=2, n=4/r=2 and n=4/r=3. P2Top/P3Top instantiate top decomposition.
These work over arbitrary set-rings D and every projective twist k.

Validation commands (from unit unless otherwise indicated):
  timeout 55 ./segc sag/zmt-cech-general all
  In sag/zmt-cech-general, with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt-cech-general.opens

Results:
  segc: 78 modules, 0 failed.
  Fresh All.seg: 3722 declarations, 0 failed (384 new), about 1.1 s.
  --opened: all 384 new declarations, at most 18 definitions opened,
            at most 0.03 s per declaration in the recorded run.
  --opens: all 384 profiles report "nothing else opened".
The audit profiles list openings of structural recursions and their
local helpers, integer normal forms, carrier/accessor aliases, the
existing regular/powM/SubMod module operations, and truncated support.
They do not open any polynomial quotient or older contraction proof.
The module-level linear maps open up to 18 representation definitions:
they explicitly identify the generic submodule operations with raw
pointwise operations. No claim of opaque abstraction at these bridges
is made.

Two deliberate mutations were rejected and restored: deleting the minus
sign in the negative-coordinate branch of h, and claiming that h raises
rather than lowers rank. The complete checks pass after restoration.

6. Limits and next integration step

This does not replace Cech4 with an equivalent module or prove a full
module equivalence to its indexed Pt/Ed/Tri/Sq representation. It proves
the characterising signs and stages the same relevant dimensions.
No sheaf-theoretic Cech comparison, polynomial action, monomial shift,
finite basis for the top projection, syzygy transport, Rees comparison,
weighted dependence, arbitrary-base descent, or full ZMT is asserted.

For the next arbitrary-dimensional ZMT milestone, combine these modules
with sag/zmt-syzygies-general. First bridge natural exponents to Laurent
exponents componentwise and prove shift/degree/chart-support laws. Then
build the finite top-coordinate module needed by the syzygy resolution,
and transport its polynomial action to this complex. The contraction and
finite-support proofs need not be reproved in each dimension.
