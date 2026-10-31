Exact multiplicative orders
===========================

FiniteOrderPowers.Over[A] works in any commutative ring. Its Exact a m
means that a has positive order m+1, in exactly the convention of
MinimalFiniteOrder. No field, nonzero-ring, or decidable-equality
hypothesis is needed by these algebraic operations.

Main interfaces:
  divisor a m exact n period
    returns q with n = q*(m+1).
  gcd-period a m n pm pn
    transfers two periods to the actual existing Euclidean gcd.
  coprime-period a m n coprime pm pn
    concludes a=1 when that gcd is 1.
  power-exact a m h u exact factor
    gives exact order u+1 for a^(h+1), where
      m+1 = (u+1)*(h+1).
  ExactProduct[a,b,m,n,ea,eb,coprime].exact
    gives order (m+1)*(n+1) for a*b, when the orders are coprime.

The exact-order minimality proof uses Euclidean division. The coprime
argument runs Euclid directly on periods, avoiding signed powers and
an auxiliary group theory library. NaturalProductOrder proves just the
positive multiplication bounds needed by these two constructions.

Validation
----------
Fresh All.seg --opened: 1810 declarations, 0 failed, 0.35 s.
./segc sag/etale-field-orders all: 57 modules, 0 failed.
Three owned files: 99 declarations; all round to 0.00 s and open at most
12 definitions. All 93 named declarations have clean .opens entries;
six anonymous opens are omitted.

FiniteOrderRegression checks the unit 3 of Z/4, its square of order 1,
its product with 1, and the quotient of its period 6 by its order 2.
A generic instance combines orders 2 and 3 into order 6. An isolated
mutation claiming that 3 in Z/4 has order 3 is rejected by the checker.

All reused files are unchanged relative links. No new axioms, checker
edits, shared edits, or commits. The finite-field maximal-order and
cyclicity assembly lives separately in etale-field-finite-primitive.
