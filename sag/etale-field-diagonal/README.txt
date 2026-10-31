Diagonal averaging certificate from formal unramifiedness
========================================================

1. Status and scope

The diagonal-idempotent milestone is proved, including the constructed
tensor product.  R is any commutative set-ring; there is no field,
flatness, etale presentation, lifting-existence, ZMT, or trace assumption.
Only the existing All.seg univalence, replacement and surjection
parameters are used.  There are no new axioms or checker changes.

All reused .seg files are relative links.  The four owned proof modules
are DiagonalKernel, FiniteKernelSquare, DiagonalCertificate and
DiagonalRegression.  Shared files and earlier developments are unchanged.
Nothing is committed.

2. Exact interface

In DiagonalCertificate.Over[R,setR], C, P, E and Tn are respectively
Algebras, Presentations, FormallyEtale and Tensor over R.

At[S,D,cp], where cp : Tn.Coproduct S S D, defines DK as
DiagonalKernel.Over[R,setR].At[S,D,cp].  Its maps are
  DK.left  = cp.1,
  DK.right = cp.2.1,
  DK.mu    = (cp.2.2 S).sec (C.identity S,C.identity S).

At.Witness is a record with fields:
  epsilon    : D.ring.R;
  mu-one     : DK.mu(epsilon) = 1;
  equalises  : for every s:S, epsilon*DK.left(s)=epsilon*DK.right(s);
  idempotent : epsilon*epsilon=epsilon.

At.theorem (fp : P.FP S) (unique : E.Unique S)
  : Truncation[l].Trunc[At.Witness].carrier.

At.Presented[p,ps,unique].theorem is the explicit-presentation form.
Concrete[p,S,ps,unique] constructs Tn.Presented[p,p,S,S,ps,ps] and exports
the same certificate for that actual tensor product.

Finally, exists S fp unique merely gives
  (D : C.Algebra) * (cp : Tn.Coproduct S S D) * At[S,D,cp].Witness.
The caller need not already supply a tensor product or choose a finite
presentation.  All presentation/matrix choices stay inside truncation.

3. Proof structure

DiagonalKernel constructs multiplication and its split surjection.  The
differences left(x_i)-right(x_i) generate its kernel J: quotient by those
differences, use presentation uniqueness to equate the two S-maps, and
then coproduct uniqueness to factor the quotient projection through mu.
Effectiveness gives the finite coefficient witnesses for every element
of J.  No expansion of tensor elements is required.

FiniteKernelSquare constructs J^2 from finite sums of the generator
differences with coefficients in J.  It proves J^2 is an ideal contained
in J; every product of two members of J belongs to J^2.  In D/J^2 the
image of J is an actual square-zero ideal with propositional membership.
This generalises the quotient construction previously internal to
EtaleCase; neither its source uniqueness nor its target lifting
hypothesis is retained.

DiagonalCertificate applies Unique S to the two maps into D/J^2.
They agree modulo the square-zero image, hence already agree in D/J^2.
The named kernel-square and square-kernel lemmas give both inclusions
J=J^2.  Finite choice supplies the matrix for IdempotentIdeal.  Its
determinant epsilon annihilates J and is 1 modulo J, which gives the
normalisation, equalisation and idempotence laws.

4. Regressions and mutations

DiagonalRegression.Empty works over every commutative set-ring and uses
the empty presentation of the base algebra.  It exercises both the
concrete and fully truncated tensor exports, including rank zero in the
determinant step.  The base is allowed to be the zero ring.

DiagonalRegression.Nontrivial uses the constructed standard algebra for
X^2-X over Z/4Z from FlatRegression.  The mixed tensor evaluation sends
the left root to 0 and the right root to 1.  It kills epsilon, whereas
mu(epsilon)=1.  Consequently the constructed epsilon is neither 0 nor 1.
The final regression closes the finite polynomial-representative choices.

Two isolated mutations in temporary copies were rejected:
  - changing mu(epsilon)=1 to mu(epsilon)=0;
  - replacing a generator difference by the sum of the two embeddings.
The working source files were never mutated.

5. Validation and opening audit

Fresh built-checker All.seg: 7317 declarations, 0 failed, 2.67 s.
176 declarations are new, counting four open directives; all 172 named
owned declarations are listed in etale-field-diagonal.opens.
Every new declaration takes at most 0.01 s and opens at most 22 distinct
definitions in the fresh --opened run.  The --opens specification is a
frozen regression audit of the actual qualified definitions opened.

Some quotient carrier/ring/projection aliases open when comparing the
concrete quotient with the algebra structure on it.  These are listed
explicitly, including the underlying image/quotient aliases; they are
not hidden behind a claim that only mathematical operation names open.
The coproduct equations are stated generically in DiagonalKernel.To
before substituting the concrete presented tensor, avoiding unfolding
its whole quotient construction in the mixed-evaluation regression.

Commands, from unit/:
  ./segc sag/etale-field-diagonal all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-diagonal/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-diagonal/All.seg \
    --opens sag/etale-field-diagonal/etale-field-diagonal.opens

6. Outside this directory

General flatness transfer is a separate development consuming Witness;
regularity over a discrete field is the root integration task.  No
finite basis, primitive-element theorem, trace pairing, or residual
coefficient/denominator bridge is asserted here.  The algebra-coproduct
API does not yet provide the module tensor-coordinate API needed to
apply coordinate functionals to the diagonal element.
