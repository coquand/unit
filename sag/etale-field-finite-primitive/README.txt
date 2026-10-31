FINITE FIELDS: PRIMITIVE ELEMENTS FROM AN EXPLICIT ENUMERATION
===========================================================

1. Checked endpoint
-------------------

FiniteFieldPrimitive.Over[K,A,setA,rho,dec,nontrivial].theorem
  Q enumerate injective onto : Data

Inputs:
  K,A       commutative rings;
  setA      A is a set;
  rho       a ring map K -> A;
  dec       for every x:A, x=0 or an explicit inverse of x;
  nontrivial  not(1=0) in A;
  Q         Ring.Nat;
  enumerate Fin Q -> A;
  injective equality of enumerated values implies equality of indices;
  onto      each x merely has an index with enumerate(index)=x.

Output Data is actual data, not truncated:
  gamma        an element of A;
  invertible   an inverse of gamma;
  lower        a list of coefficients in K;
  root         monic(lower) evaluates to zero at gamma;
  slope-unit   the dual-number Horner slope at gamma has inverse -1;
  representation
               for every x:A an actual coefficient list p over K with
               Horner(rho,gamma,p)=x.

monic appends coefficient 1 to the end of the list, in the existing
MonicReduce/SelectedFactorStatement convention. The derivative is expressed
as the second component of evaluation at (gamma,1) in the dual numbers;
there is no unproved identification with a separate derivative operation.
The list is T^Q-T. Its coefficients 0,1,-1 work over any supplied base K;
no field assumption on K is needed.

The theorem proves internally that Q is at least two. It uses only unique
preimages to eliminate the merely-surjective enumeration. It makes no
choice of representatives and assumes no factorisation, characteristic
classification, primitive-element principle, or finite-group theorem.

2. Proof, backwards from the endpoint
-------------------------------------

A multiplicative generator gamma gives a polynomial representation of any
nonzero element as a power of gamma; zero is represented by the empty list.
For separability, it suffices to show x^Q=x and Q*1=0, since T^Q-T has slope
-1. Both identities are obtained directly by reindexing the enumeration.

For the generator, bounded search computes exact positive orders. A finite
maximum gives gamma of maximal order M. Combining gamma with any unit gives
an exact order L which is a multiple of both original orders. Maximality
implies L<=M, hence L=M, so every unit satisfies x^M=1. The first M powers of
gamma are distinct. An omitted unit would then give T^M-1 at least M+1
distinct roots, contradicting the checked sharp root bound. Decidable finite
search returns the actual power index.

The order-combination step avoids prime factorisation. Write m=d*m0 and
n=d*v for gcd d, with m0 and v coprime. Starting u=m, repeatedly remove
gcd(u,v)>1 from both u and d. The quotient u strictly decreases. The result
is m=h*u', n=d'*(h*v), with u' coprime to h*v. Thus a^h and b^d' have coprime
exact orders u' and h*v, and their product has an exact common-multiple
order. Instead of tracking h|v^k, the proof tracks the simpler property

  Support(h,v) := forall r, Coprime(r,v) -> Coprime(r,h).

The existing ZArith Euclidean algorithm supplies integer Bezout identities;
signed-magnitude uniqueness converts its quotient coefficients into actual
natural quotients. No new arithmetic axiom is introduced.

3. Module APIs and boundaries
----------------------------

PolynomialRootBound.Over[A].Field[inverse].theorem
  n p bound x injective roots : coefficientwise p=0.
Bound n p means degree<n. Synthetic division removes one root.
.Search[zero-dec].nonvanishing returns an actual index with nonzero value
from a known nonzero coefficient and n distinct candidate values.

FinitePermutationFold:
  finite folds in a commutative monoid, selector matrices, exchange of two
  folds, invariance under a permutation with an explicit inverse, and a
  constant fold with one omitted coordinate. No permutation decomposition.

FiniteFieldEnumeration:
  the fibres of an injective enumeration are propositions, yielding actual
  inverse indices from truncated surjectivity.

FiniteFieldPowers.Over[A,setA,dec,nontrivial].At[n,enumerate,index,ei,ie]:
  cardinal-zero: (n+1)*1=0;
  Nonzero[a,unit].fermat: a^n=1;
  frobenius x: x^(n+1)=x.
  Translation reindexes the sum. Multiplication by a unit reindexes the
  product in which the zero coordinate has been replaced by 1.

FrobeniusPolynomial:
  actual coefficient lists, degree, leading coefficient, ordinary Horner
  evaluation, and dual-number slope computation for T^(m+2)-T.

FiniteFieldAnnihilator.Over[K,A,setA,rho,dec,nontrivial].Enumerated
  [Q,enumerate,injective,onto]:
  one common lower coefficient list, root x and separable x for every x.

MinimalFiniteOrder.Over[A].Exact a m:
  a^(m+1)=1 and every r<m+1 with a^r=1 is zero.
  At[a,decide-powers].theorem gives the least positive order by bounded
  search from a known positive closing exponent, including an order bound.

FiniteFieldMaximalOrder.Over[A,setA,dec,nontrivial].At
  [m,enumerate:Fin(m+2)->A,injective,onto]:
  gamma, invertible, predecessor, gamma-order, and
  dominates a unit : (j)*(Exact a j * Le j predecessor).

NaturalGcd:
  natural quotients and positive-divisor cancellation around ZArith.euclid.
  Cofactors gives integer Bezout for the two normalized quotients.

CoprimeArithmetic:
  Bezout under products and divisors, Support, coprime cancellation, and
  gcd-one converting integer Bezout into (ZArith.euclid m n).g=1.

GcdStripping.theorem u d m v unz dnz relation coprime:
  actual h,u',d', equations u=h*u', d=h*d', u'=d'*m,
  Coprime(u',v), Support(h,v), hence Coprime(u',h*v).

CoprimeOrderParts.theorem mp np:
  for orders m=mp+1,n=np+1, actual positive h,d,u,w with m=h*u,n=d*w,
  Coprime(u,w), and u*w an explicitly witnessed multiple of both m and n.

OrderCombination.Over[A].At[a,b,m,n,ea,eb]:
  element, predecessor, exact order, inverse, and two common-multiple laws.
  Reuses the checked exact-power and exact-coprime-product theorems from
  ../etale-field-orders/FiniteOrderPowers.seg unchanged.

MaximalOrderPeriod:
  maximal exact order implies a common exponent for every unit.

FinitePowerOrbit:
  finite ordinal indices and pairwise distinct powers below an exact order.

FiniteEqualitySearch:
  actual decidable membership in a finite family.

FiniteFieldCyclic:
  exact order plus a common exponent implies every unit is one of the first
  powers, using PolynomialRootBound. Returns an actual index.

FiniteFieldPrimitive:
  the complete assembly stated in section 1.

4. Reuse and assumptions
-----------------------

Every reused file is a relative link. The new development has nineteen
owned proof/regression modules and All.seg. It reuses the existing
univalence, replacement, and surjection parameters of All.seg. No new axiom
or shared/checker modification is present. Nothing was committed.

NaturalProductOrder and FiniteOrderPowers are linked from the concurrent
etale-field-orders development. ZArith, Integers, NatOrder, polynomial,
truncation, and dual-number libraries are reused unchanged.

5. Validation
-------------

Fresh built-checker All.seg: 2289 declarations, 0 failed, about 0.6 s.
./segc sag/etale-field-finite-primitive all: 67 modules, 0 failed.

There are 812 owned declarations (757 generic and 55 regression).
--opened:
  generic declarations: at most 21 definitions opened, at most 0.02 s;
  regressions: at most 67 definitions opened, at most 0.10 s.
--opens etale-field-finite-primitive.opens:
  all 812 owned declarations covered; "nothing else opened" for each.

Regressions:
  * Actual F2 with an explicit injective/surjective enumeration: the complete
    primitive-element theorem, representations of both elements, a root,
    and invertible slope. The maximal generator is proved to be 1.
  * The computed lower list is [0,1], so the monic polynomial is T^2+T.
  * Orders 6 and 4: computed factors h=2,u=3,w=4, common order 12.
  * Orders 8 and 16: the actual construction instantiated and its two
    factorisations and coprimality checked. This exercises repeated gcd
    stripping in the construction but does not normalize the whole output.
  * Orders 1 and 1, including computed remaining factors.

Three deliberate mutations were rejected, restored and rechecked:
  * change the generic slope -1 to +1;
  * change the leading coefficient of T^M-1 from 1 to 0;
  * change the computed removed factor for orders 6,4 from 2 to 3.

6. Limits
---------

This theorem starts with a finite enumeration of the field A. It does not
construct a selected field factor from a finite algebra or an enumeration
from a finite-dimensional algebra over a finite base. Those are separate
interfaces being developed elsewhere.

There is no F4 or larger-field concrete regression in this directory; the
nontrivial order arithmetic is tested independently. Attempting to reduce
all output integers for the orders 8,16 by definitional equality exceeded
our per-declaration test budget, so those checks use named proved laws.
This limitation is confined to eager normalization of regression outputs;
all generic declarations stay within the bounds above.

The primitive generator is produced by finite search and gcd arithmetic.
No claim is made about its optimal computational complexity.
