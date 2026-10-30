Generic polynomial action and finite top coordinates
===================================================

1. Result and ownership

This integration directory constructs finite polynomial multiplication on
the generic Laurent/Cech modules, arbitrary finite shifted homogeneous
matrix actions, and finite coordinates detecting the top residual pi.
All constructions work over any commutative set-ring D, with any finite
number n of homogeneous coordinates. No field or CFN hypothesis is used
by these constructions.

The directory contains 15 new .seg files, 520 new declarations. Every
older imported file is a relative link. Sources in zmt-cech-general,
zmt-syzygies-general, zmt-certificate-general, earlier ZMT4 developments,
shared libraries, checker files and .git were not modified. Nothing is
committed. There are no new axioms, resizing assumptions or infinite
choices; All.seg uses the existing foundational parameters.

Related work supplied by the parallel certificate agent is imported by
relative links: ChartDenominators, PolynomialCoefficientParts,
ChartPolynomialization, LaurentPolynomialCoefficients, TowerLaurentAction.
In particular, the actual ring-product/action comparison is proved in
TowerLaurentAction, and local denominator clearing is proved on arbitrary
chart intersections, not just the fully inverted chart.

2. Convention and types

Natural exponents are FiniteExponents.Exp n = Fin n -> Base.Nat.
Laurent exponents are GenericLaurent.Exp n = Fin n -> ZInt.Int.
Old coordinates have index inl i; the newest coordinate is inr tt.
The generic Cech orientation puts this NEWEST vertex FIRST, as before.
The Laurent projective degree is the recursive sum newest + old total.

In GenericCech, cochain rank r is integer subset-cardinality. Ordinary
Cech degree q corresponds to r=q+1. Rank 0 is the polynomial augmentation.
The n=0 construction is this augmented one-term complex; no projective
P^(-1) interpretation is claimed.

A polynomial is an ordinary finite term list List(D.R * natural exponent).
Its multiplication on coefficients is
  mulP p f m = sum_(c,u in p) c * f(m-u).
The iterated polynomial coefficient-ring tower is compared through its
existing phi and Coeff maps. Equality of tower images implies equality
of the action. There is no need to package a redundant ring equivalence.

3. Files and precise informal proof

LaurentExponentBridge
  At[n].emb maps natural entries to pos entries. At[n].addE and subE
  apply addP and natural predecessor iteration componentwise.
  add-sub, sub-add, sub-sub, sub-comm, sub-add-comm follow by exponent
  function extensionality and the corresponding one-variable identities.
  deg-sub/deg-add follow by induction on n and add-minus2/add-addP2.
  flag-minus says subtracting a natural preserves a negative integer;
  Mono and mono-bad lift this sign implication to the recursive chart
  predicate. Thus bad-sub proves chart support is preserved.

FiniteLaurentAction
  This generalises the finite-sum/expansion argument of PolynomialAction4,
  using generic exponents and the proved translation identities. The
  selected-coefficient functions monoD and list/nub utilities of the old
  file are reused, because those utilities do not depend on dimension.
  mulP-cong/zero/add/neg/sm/sub are list inductions. Concatenation is sum;
  scaleT and pmul form every product of terms, and mulP-pmul proves
  multiplication composition using sub-sub. psum and mulP-psum handle
  finite families. mulP-shift handles commuting translations.
  For coefficient invariance, expand each polynomial over the nub of its
  exponent support. The single-term selection sum contributes precisely
  once, so expand is valid without deciding equality in D. A zero
  coefficient polynomial acts by zero (act-zero); applying this to p-q
  proves act-coef. No monomial basis is assumed.

CechPolynomialAction
  Shifts(k,k',p) requires k'-degree(u)=k for every term of p; Hom(e,p)
  requires each degree(u)=e. hom-shifts constructs the former from the
  latter for k'=k+e, including all integer degree cases.
  suppL translates the original finite support by each term's exponent.
  vanish-mulP uses (m-u)+u=m to show this finite list is a support.
  not-degree and bad-sub combine the total-degree identity, chart
  monotonicity, and unchanged subset-cardinality. van-mulP proves the
  resulting actual cochain condition. Act builds the actual target
  cochain and its D-linear map lin; val states its coefficient formula.
  d-comm proves d(p c)=p d(c) by structural subset induction, using
  d(a,b)=(da,a-db) and mulP-sub. Ambient exponent dimension is fixed
  independently of this induction. Comm.equation is equality in the
  actual target cochain module. No commutation with h or pi is asserted.

ShiftedMatrixAction
  Family[a,k,r] is the finite product of cochains of twist k_i and rank r.
  Differential applies the already constructed d in each component.
  Matrix constructs each polynomial entry via Act, each row by a finite
  sum, and the matrix by the product universal construction. Comm proves
  d(H z)=H(d z) using linearity of d on each finite row sum and the
  previously proved entry commutation. HomShift and shifts implement
  the standard k-d_i convention for natural free-module shifts.

FiniteExponentBoxes
  range(b) lists 0 through b. range-cover proves completeness from a
  complementary summand x+r=b. boxes(n,b) is its n-fold cartesian product.
  box-cover proves it contains every vector with degree(u)+r=b: the head
  and the old coordinates are each bounded by b, by associativity and
  commutativity of natural addition. This avoids introducing order or
  quotient-ring equality into the enumeration proof.

FiniteTopExponents
  negative(n,u) has entries -(u_i+1); mass(n,u)=degree(u)+n.
  degree-negative proves its total degree is negPos(mass). Therefore a
  monomial of twist k has mass=magnitude(k). It belongs to the finite
  box with side magnitude(k). Filter that box by the actual integer
  equality total(negative(u))=k to construct naturals; exponents is its
  Laurent image. cover proves every all-negative monomial of twist k
  occurs. The list depends only on n,k and never on an input cochain.

NegativeClassification
  classify structurally gives either an explicit negative(n,u)
  representation or a coordinate with nonnegative sign. zero-some proves
  that the latter forces the residual pi to be zero on every raw family.

FiniteLookup
  A list has coordinates Fin(length list); at gives each coordinate's
  exponent. lookup selects the first equal entry, using only natural
  exponent equality. read-inside reconstructs an extracted coefficient
  at every list member; read-outside is zero elsewhere. zero proves that
  zero coordinate values reconstruct to zero. Repetitions are harmless:
  this is a finite presentation, with no minimal-basis claim.

FiniteTopPresentation
  Extract pi(c) on the negative exponents in the constructed static list.
  extractlin is a D-linear map into the actual finite free module D^rank.
  Reconstruction is zero on proper subsets, zero off degree k, zero if
  there is a nonnegative coordinate, and otherwise first-match lookup.
  equation proves reconstruct(extract(c))=pi(c): use top-only support,
  projective degree, negative classification, cover, and read-inside in
  the respective branches. top-zero follows from equation and zero.

FiniteFamilyCoordinates and ShiftedTopPresentation
  Flatten blocks of sizes rank_i using the existing finite-sum index
  maps Blocks.ix/xi. inject keeps the summand tag; at-inject recovers its
  coordinate. relates and operation prove flattening respects equalities
  and pointwise operations. ShiftedTopPresentation therefore constructs
  a single D-linear finite vector for an arbitrary shifted family,
  reconstructs every summand pi, and proves the combined top-zero test.

PolynomialActionTowerComparison
  Compare the finite action's coefficient selection with the existing
  PolynomialTowerBridge.cf by induction over the term list. This gives
  coefficient-ring and invariant. action applies the separately checked
  TowerLaurentAction comparison: Laurent multiplication by p agrees with
  the coefficients of multiplication by phi(p) in the constructed tower.

TopEnumerationSoundness
  good proves that every retained natural vector has exactly degree k;
  negative-mask proves all its Laurent entries are negative. degree/sign
  apply these facts to each Fin-indexed coordinate. full-proj proves pi
  is identity on an all-negative monomial. Coordinates.value consequently
  identifies extraction with the literal original top coefficient of c.

ActionComposition
  degree-add and degree-emb prove the natural/Laurent degree bridges.
  app-shifts, scale-shifts and product-shifts CONSTRUCT the degree witness
  for a product from those of its factors. Compose.equation lifts
  mulP-pmul to equality of actual cochains; Invariant.equation similarly
  lifts coefficient invariance. Their main laws are not record parameters.

4. Public API

LaurentExponentBridge.At[n]
  emb, addE, subE, add-sub, sub-add, sub-sub, sub-comm, sub-add-comm
LaurentExponentBridge
  deg-add, deg-sub, bad-sub
ActionComposition
  degree-emb, degree-add

FiniteLaurentAction.Over[D,setD,n]
  Polys, mulP, coef, scaleT, pmul, psum
  mulP-add/sm/sub/pmul/psum, act-zero, act-coef

CechPolynomialAction.Over[D,setD,n]
  Hom e p, Shifts k k' p, hom-shifts
  Act[k,k',r,p,hp].lin : Lin(C(n,k,r), C(n,k',r))
  Act[...].val : the exact finite polynomial coefficient formula
  Comm[k,k',r,p,hp].equation : d(p c)=p d(c), actual cochain equality

ActionComposition.Over[D,setD,n]
  product-shifts, Compose[...].equation, Invariant[...].equation

ShiftedMatrixAction.Over[D,setD,n]
  Family[a,k,r].mod
  Differential[a,k,r].lin
  Matrix[a,b,ko,ki,H,hH,r].lin
  Comm[a,b,ko,ki,H,hH,r].equation
  HomShift, shifts (natural free-module shift convention)

FiniteTopPresentation.Over[D,setD,n,k]
  rank : Nat; free = D^(Fin rank)
  extractlin : Lin(C(n,k,topRank n), free)
  equation c s m : reconstruct(extract c)(s,m)=pi(c)(s,m)
  top-zero c hz s m : pi(c)(s,m)=0 if every extracted coordinate is zero

ShiftedTopPresentation.Over[D,setD,n,a,k]
  rank, free, lin, at-tag, equation, top-zero
  The tags are (summand i, local coordinate j), embedded in Fin rank.

PolynomialActionTowerComparison.Over[D,setD,n]
  coefficient-ring p u : Coeff(phi(p))(u)=coef(p)(u)
  invariant p q e f m : equal tower images give equal actions
  action p x m : mulP(p,coeff(x))(m)=coeff(phi(p)*x)(m)

The local chart APIs supplied by the certificate agent are linked here:
  ChartDenominators.Clear[n,s,support].bad-up/bad-down, outside-up/down
  ChartPolynomialization.Over[...].Clear[...].cleared
  LaurentPolynomialCoefficients.Over[...].At[n].coeff
  TowerLaurentAction.Over[...].At[n].action
Consult that directory's README for their full parameter signatures.

5. Validation and regressions

Commands from unit:
  timeout 55 ./segc sag/zmt-cech-action all
From sag/zmt-cech-action, with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt-cech-action.opens

Recorded results:
  segc all: 148 modules, 0 failed.
  Fresh All.seg: 8316 declarations, 0 failed, about 3.7 s.
  New local source declarations: 520, in 15 files.
  --opened: at most 26 definitions opened and 0.01 s per new declaration.
  --opens: all 520 local profiles report "nothing else opened".
The profiles include structural finite-list/sign/degree recursions;
raw and submodule carrier/accessor/operation aliases; product/finite-sum
module operations; and, at the tower bridge, its coefficient-ring carrier
aliases (CoefficientTower, GradingStep.S, PolynomialRing.Extension and
the quotient carrier). The latter identify the theorem's tower ring;
no quotient representative is selected or polynomial proof is unfolded.

ActionRegression checks n=0 top ranks at twist 0 and positive twist,
n=1 top rank at twist -2, concrete multiplication by the newest/first X_0
in four coordinates, multiplication composition, a one-by-one polynomial
matrix commuting with d, coverage of (-1,-1,-1,-1) at twist -4, actual
four-coordinate reconstruction/top-zero, the empty shifted family, two
tagged top summands, and the four-coordinate tower-action comparison.
GenericRegression from the previous milestone still checks the matching
edge/triangle/tetrahedron Cech signs. No equivalence to the older Cech4
representation is inferred from these comparisons.

Two mutations were rejected and restored: replacing the action's m-u
translation by m+u, and reconstructing a nonzero value on proper subsets.
The complete module check passes again after restoration.

6. Limits and next step

The finite top presentation is deliberately generous and need not be a
minimal basis. Reconstruction is a raw coefficient function; its equality
to pi on extracted cochains is proved coefficientwise. Extraction is an
actual D-linear map to a finite free module. No global choice of polynomial
term representatives is made. Main degree, action, commutation and
finite-coordinate laws are proved, rather than assumed as record fields.

Selected h is only D-linear: it is NOT asserted to be polynomial-linear.
This directory does not compute kernels of the top matrix or prove full
ZMT, Rees comparison, arbitrary-base descent or weighted dependence in
arbitrary dimension. The certificate integration must use its constructed
homogeneous kernel stages, localised syzygy lifts and these top-coordinate
maps to build the resolution certificate and final sequence dependence.
