Full product structure over a discrete field
===========================================

1. Checked endpoint

  UnramifiedFieldProduct.Over[k,setk,field].At[S,fp,unique].theorem

Hypotheses:
  - k is a commutative set-ring with a zero-or-unit operation and 1 != 0;
  - S is a k-algebra;
  - fp : Presentations.Over[k,setk].FP S (mere finite presentation);
  - unique : FormallyEtale.Over[k,setk].Unique S (uniqueness of
    square-zero lifting, i.e. formal unramifiedness).

Conclusion:
  merely ProductPresentation.Over[k,setk].At[S].

This certificate contains a finite binary tree of monic polynomials,
an inverse of the derivative in every monic quotient, and an actual
algebra isomorphism from their product to S. Both directions are algebra
maps, with both inverse equations. No prime, basis, trace certificate,
primitive element, factorisation oracle or ZMT principle is an input.

This is the full product theorem, not just the selected-prime theorem
in etale-field-complete. The polynomials are separable but are not
asserted irreducible. Thus the factors are monogenic finite etale
algebras; they are not asserted to be fields over the original k.

2. Product representation

MonogenicPresentation.At[S] records the concrete monic quotient Q,
algebra maps Q -> S and S -> Q, both inverse equations, and an inverse
of f' in Q. Q is the existing MonicBasisUniversal quotient.

ProductPresentation.Shape has constructors single(lower) and pair(t,u).
Its interpretation is the actual recursively constructed product ring,
with componentwise operations. At[S] records the shape, separability
of all its leaves, and AlgebraIsomorphism.Iso[algebra shape,S].

The zero algebra is allowed. A leaf with polynomial 1 represents it.
Zero pieces need not be discarded. There is no claim that the returned
tree has a minimal number of factors or that its leaves are connected.

3. Large-field simplification

The existing DiagonalSeparator constructs x and w with
  Delta(x)*w = 1-epsilon.
SeparatorMonogenic now proves x globally generates S. This bypasses
the selected relative-basis and selected-coordinate arguments.

For the minimal monic annihilator f, of degree m > 0, define
  H(X,Y) = (f(X)-f(Y))/(X-Y)
by Horner recursion. This is a polynomial identity, not division in the
tensor algebra. It gives
  H(left x,right x) = epsilon * right(f'(x)).
Minimality and the existing Gaussian quotient construct a linear
functional lambda killing the powers below m-1 and sending x^(m-1)
to 1. Contracting the left tensor factor gives
  1 = f'(x) * contraction(epsilon),
an explicit derivative inverse. No regularity is used for this step.

The minimal quotient Q=k[T]/f embeds in S. Reducedness and its finite
basis make Q regular. An injective map from a regular ring reflects
units, so the derivative inverse belongs to Q. Horner recursion gives
Q-preimages of the tensor coordinates of H and then of epsilon. The
trace identity gives Q-preimages of every element of S. The existing
MinimalPolynomialInjection.Monogenic constructs the inverse algebra map.
The degree-zero case is covered using the equation 1=0.

Relevant files:
  FieldSeparatingFunctional, MinimalPowerFunctional,
  MonicDividedDifference, TensorDividedDifference,
  TensorMonicContraction, SeparatorDerivativeUnit,
  RegularUnitReflection, TensorPolynomialCoordinates,
  SeparatorMonogenic, LargeFieldMonogenic.

4. Small-field construction

FiniteMonicCoefficientFamily and FiniteCoefficientField are reused.
The small branch supplies an actual finite coefficient field K0 and
monic equations over K0 for the ambient basis. MonicFiniteImage then
constructs the finite reduced algebra B=K0[basis_i] inside S, including
its enumeration and its own regular witnesses.

FiniteRegularRefinement splits by a*b and 1-a*b for every enumerated
a, where a=a^2*b. On one piece a is a unit; on the other it is zero.
Previously resolved equations survive refinement. The induction is on
the finite enumeration length, so no dimension-decrease theorem or
prime ideal is needed. Finite choices remain inside truncation.

FiniteResolvedField constructs a zero-or-unit operation on each final
corner and deduplicates its enumeration. Each nonzero corner is an
actual finite field. FiniteFieldPrimitive supplies a primitive element
and polynomial representatives for all its elements. These give
representatives of every projected ambient basis vector in eS.

IdempotentMonogenicSpan passes the ambient basis, reducedness and trace
nondegeneracy to eS. PolynomialSpanGeneration gives generation of all
of eS. GeneratedSeparableMonogenic constructs its minimal-polynomial
isomorphism and proves separability using the checked trace theorem.

IdempotentProductIsomorphism constructs
  eS = efS x e(1-f)S
with projections and addition as inverse maps. ProductsOnIdempotents
glues both branches. SmallFieldProduct retains every branch, including
zero pieces. FiniteEtaleProduct combines the two coefficient-field
branches, and UnramifiedFieldProduct supplies all structural inputs.

5. Regressions

ProductRegression checks:
  - F2 from finite presentation and Unique, with no supplied basis;
  - the actual standard algebra for X^2-X, from the same hypotheses;
  - the large branch with the constructed tensor diagonal and separator;
  - the small branch on the coordinatewise algebra F2^m, with its actual
    delta basis, trace nondegeneracy and monic equations X^2+X;
  - m=3, where one global generator cannot suffice;
  - m=0, the zero algebra.

The generic F2^m regression invokes the complete small-field branch:
finite image, regular refinement, finite field primitive elements,
minimal quotients and product isomorphisms. It does not supply a product
presentation to the theorem. The tests check proof terms, not extraction
and normalization of the whole returned truncated binary tree.

Three mutations in isolated temporary copies were rejected:
  - replacing X by Y in the divided-difference recursion;
  - replacing the complementary branch by the positive support;
  - dropping the derivative inverse from the tensor-cofactor preimage.
The working files were never mutated for these tests.

6. Validation (31 October 2026)

  Fresh built checker, All.seg --opened:
    18757 declarations, 0 failed, 9.42 s.
    847 new declarations in 25 owned modules; 17910 reused declarations.
    Each new declaration: at most 0.03 s, at most 18 definitions opened.

  ./segc sag/etale-field-product all:
    446 modules, 0 failed, 8.32 s.

  Fresh All.seg --opens sag/etale-field-product/etale-field-product.opens:
    18757 declarations, 0 failed, 10.99 s.
    All 797 named new declarations: "nothing else opened".
    The other 50 declarations are open/structural declarations.

The checking server was stopped after validation. Nothing is committed.
No shared Unit source, earlier development or checker source was edited.
Dependencies are relative links to the existing checked developments.
There are no new axioms: All.seg retains the existing Theory parameters
univ, images and surjections. The final theorem has no ZMT premise.

7. Documentation and scope

The informal shortcut and full product proof are described in
  doc/etale-field-reduction.tex (and rebuilt PDF).
The status and endpoint are also recorded in
  doc/etale-local-proof.tex (and rebuilt PDF).

The product is a finite binary tree, not a flat Fin-indexed family.
No optimisation removes zero factors. Decomposition into irreducible
field extensions is not asserted over an arbitrary discrete field.

The existing selected-factor local adapter is unchanged. Integrating
the product theorem into the original local factor-selection proof,
and supplying all original local hypotheses to that proof, remain
separate work. In particular this milestone does not assert that the
unconditional local flat + unramified => etale theorem is now assembled.

8. Recheck

From unit/:
  ./segc sag/etale-field-product all
  ./segc sag/etale-field-product stop

Fresh checker:
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-product/All.seg --opens \
    sag/etale-field-product/etale-field-product.opens
