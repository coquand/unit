Polynomial extension of a finite algebra basis
=============================================

1. Statement and exact interface

PolynomialBasis.Over[k,setk,S,n,b] takes any commutative set-ring k, a
k-algebra S, and b:TraceBasis.Over[k,setk,S].Basis[n]. No field,
reducedness, unramifiedness or nonzero-rank assumption occurs.

K = PolynomialRing.Extension[k,setk],
P = PolynomialRing.Extension[S.ring,S.set].
scalar:K.ring -> P.ring is exactly FlatPolynomialData.Map.f, obtained by
Universal.Property from the constant map composed with S.iota and the
variable of P. algebra is P as a K-algebra through scalar.

basis:TraceBasis.Over[K.ring,K.set,algebra].Basis[n] has vector j equal
to P.constant(b.vector j). Its coordinates satisfy:
- coordinate-constant a i: coordinate(P.constant a)i =
  K.constant(b.coordinate a i).
- coordinate-variable p i: coordinate(P.variable*p)i =
  K.variable*coordinate(p)i.
- coordinate-list p i: coordinate(P.include p)i =
  K.include(coordinateRaw p i), where coordinateRaw applies b.coordinate
  to every coefficient and preserves the list order.
- coordinate-add, coordinate-scale, reconstruction and on-vector are
  the explicit basis laws.

PolynomialBasisBounds.Over[k,setk,S,n,b] proves:
- raw-length: coordinateRaw preserves the coefficient-list length.
- coefficient i d p: coef_K(coordinate(p)i,d) =
  b.coordinate(coef_S(p,d),i).
- bound d p h i: any FlatPolynomialData.Coefficients[S].Bound d p is
  retained by coordinate(p)i. Bound d means all coefficients at indices
  greater than or equal to d vanish.
- raw-bound p i: coordinate(P.include p)i has bound length(p).

2. Construction

FiniteBasisScalarExtension constructs the algebra of coordinate vectors
K^n using the multiplication table of S. The polynomial universal property
gives a ring map P -> K^n, mapping constants to their basis coordinates and
the variable to the scalar variable. FiniteBasisEvaluation constructs the
reverse map by summing the constant basis vectors times the coordinates.
Their composite on P fixes constants and the variable, so universal
uniqueness makes it the identity. This proves reconstruction. The forward
ring map's laws give addition and scalar multiplication. Raw Horner
recursion proves the coefficient-list formula; quotient induction proves
the coefficient formula, hence bounds without choosing representatives.

3. Regressions and validation

PolynomialBasisRegression uses the actual rank-one basis over Z/4Z on
the polynomial with coefficient list [2,3,1]. It checks this list, its
coefficient 3 at index 1, bound 3, multiplication by the variable and
reconstruction. The zero algebra's rank-zero basis also extends; every
polynomial there is proved zero by reconstruction.

Fresh All.seg: 7802 declarations, 0 failed, 3.05 s.
segc all: 184 modules, 0 failed, 2.63 s.
77 owned declarations, including 6 open declarations; all 71 named owned
declarations are listed in etale-field-polynomial-basis.opens and each
reports "nothing else opened". At most 27 definitions open, and at most
0.07 s is used by any new declaration. The operation aliases of the
existing polynomial quotient ring sometimes open; they are listed in the
audit specification. Two isolated mutations failed as expected: changing
the variable-shift formula to multiplication by 1, and changing the
computed coefficient 3 to 2. Original files were never mutated.

From unit/:
  ./segc sag/etale-field-polynomial-basis all
Fresh checker from this directory:
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opened
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opens etale-field-polynomial-basis.opens

4. Scope

The basis and its polynomial coefficient bounds are constructed, not
supplied as additional assumptions. The original finite basis of S is an
input, as intended. Evaluation of coordinates at a scalar, a nonzero
determinant value, and primitive-element generation are separate bridges.
This directory makes no assertion that the full primitive-element or
residue-field theorem is finished.

All reused .seg files are relative links. No new axioms, checker edits,
shared-file edits or changes to earlier developments were made. The
existing univalence, images and surjection parameters are inherited from
the reused All.seg. Nothing is committed.
