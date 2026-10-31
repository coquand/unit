Selected separable annihilators
===============================

Complete and checked, 2026-10-31. For a specified element of a finite
reduced algebra over a discrete nonzero field, perfect multiplication
trace yields a monic annihilator with an explicit derivative inverse on
one idempotent factor outside a specified prime. The construction also
provides one common such factor for any finite family of elements.

No shared source or checker was modified. Reused files are relative links.
No new axioms or hidden theorem parameters were introduced. Nothing is
committed. The foundational parameters remain those of the earlier All.seg.

1. One-element theorem

SelectedSeparableAnnihilator.Over[
  k,setk,field,S,n,basis,reduced,perfect,q].theorem x
  : || Result[x] ||

Inputs:
  k: commutative set-ring with the existing Field record (zero-or-unit
     decision and 1 != 0);
  S: k-algebra with an actual finite k-basis;
  reduced: a*a=0 implies a=0;
  perfect: an inverse for the determinant of its trace Gram matrix;
  q: specified proper prime with propositional, decidable membership;
  x: the specified element of S.

Result fields:
  idempotent, square, outside;
  lower: coefficients of a monic polynomial f=monic(lower);
  annihilates: f(x)=0 in the original S;
  root: e*f(x)=0;
  inverse: w in the original S;
  separable: e*(f'(x)*w-1)=0.

The derivative is exactly SelectedFactorStatement's ordinary dual-number
Horner derivative, including its coefficient-list convention. The result
does not claim that x generates eS. Primitive-element existence remains
a separate step.

For a supplied actual minimal polynomial f, At[x].Given[f].theorem keeps
f.lower unchanged. The general theorem constructs f using MinimalPolynomial.

2. Proof chain

MinimalPolynomialInjection constructs the actual finite monic quotient
Q=k[T]/f and its injection into S, sending T to x. Reducedness, regularity
and the specified prime pull back along this injection.

SelectedFiniteAlgebraBasis constructs e outside that prime and an actual
eQ-basis of eS. Its companion supplies actual k-bases of eQ and eS.
TraceRetraction transfers nondegeneracy from S to eS. TraceTransitivity,
the relative basis and the restricted injection transfer it from eS to eQ.

For a derivative annihilator a in eQ, MonicRelativeDerivation constructs
D:Q->eQ with D(T)=a. The monic universal map is compared with the canonical
projection and the relative derivation is retargeted along that proved
comparison. IdempotentDerivation restricts it to a self-valued derivation
of eQ. TraceDerivations forces it to vanish, hence a=0.

Apply this to the projected complement 1-f'*b from the constructed regular
witness f'=f'^2*b in Q. This gives a derivative inverse in eQ. Mapping the
equation into S and using derivative naturality gives the required explicit
ambient equation. No monogenic presentation of eQ is assumed.

3. Common finite factor

CommonSeparableFactor.Over[same inputs].Family[t,x].theorem
  : || Family[t,x].Result ||

The Result has one idempotent outside q, and finite families of lower
coefficient lists and inverse elements. Every x_i has its original monic
annihilator and derivative inverse equation on this common factor.

The construction first applies the one-element theorem independently in
the original S. Finite choice occurs inside truncation. Multiply the
resulting idempotents. The product remains idempotent and outside q, and
explicit divisibility by each factor preserves all its zero equations.
No repeated trace descent, further quotient or further basis construction
is needed. The empty family produces the idempotent 1.

basis-family is the specialization to the given basis vectors of S.

4. Owned sources

MonicSlopeNaturality.seg
  Monic derivative naturality by the proved recursive slope formula,
  and comparison with the ordinary coefficient-list derivative.
  An equivalent naturality helper subsequently became available in the
  reused MonicDualValues; this small local proof is independently checked.

SelectedMonicSeparable.seg
  The generic monic-quotient factor argument: selected nondegenerate trace
  plus regularity gives the projected derivative unit.

SelectedSeparableAnnihilator.seg
  Constructs the minimal quotient, the selected bases and trace descent;
  exports the one-element result with an ambient inverse witness.

FiniteIdempotentProduct.seg
  Finite product, idempotence, outside-prime proof, explicit divisibility
  and preservation of equations killed by an individual factor.

CommonSeparableFactor.seg
  Finite-family and basis-family assembly.

SelectedSeparableRegression.seg
  Concrete full constructions over F2 x F2.

5. Regressions and checks

The regression uses the actual split algebra F2 x F2, its finite basis,
computed perfect trace and prime from the first projection. It applies
the full one-element theorem to (1,0), 0 and 1. It also applies the theorem
to the already constructed minimal polynomial of (1,0), and checks that
the lower coefficients are retained and the derivative-unit equation has
the required exact type. No old handwritten selected certificate is used.

Common-factor regressions cover both basis elements, repeated elements,
and the empty family. A concrete product (1,0)*1 computes to (1,0), remains
outside the prime, and kills the nonzero other component.

From unit/:
  ./segc sag/etale-field-selected-separable all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-separable/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-separable/All.seg \
    --opens sag/etale-field-selected-separable/etale-field-selected-separable.opens

Fresh All.seg: 10181 declarations, 0 failed, 4.47 s.
segc all: 241 modules, 0 failed, 3.95 s.
Six owned modules: 203 declarations including 12 open directives.
All 191 named owned declarations have opens specifications, each clean.
Maximum owned declaration: 0.05 s and 76 definitions opened.
Fresh invocations used an external 60-second bound.

Two isolated mutations were rejected:
  replacing 1-f'*b by 1 in the regular-complement argument;
  claiming the concrete common product is 1 instead of (1,0).
The working files were never mutated.

Logs: /private/tmp/etale-field-selected-separable-{opened,opens,all}.log
and /private/tmp/etale-field-selected-separable-mutation-{complement,product}.log.

6. Remaining scope

This result supplies separate separable annihilators on one common factor.
It does not construct one primitive generator for that factor, a global
decomposition, or the final SelectedFactorStatement.Selected generation
certificate. Large-field selection and the finite-field alternative remain
downstream tasks. Reducedness, the finite basis and perfect trace are the
explicit intended field-structure inputs.
