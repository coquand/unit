Selected factor bases
=====================

Complete and checked, 2026-10-31. The generic export constructs an actual
basis of eS over eA from finite k-bases of A and S, a k-algebra map A->S,
regularity of A, and a specified decidable proper prime of A. The
idempotent e outside that prime is constructed by SelectedGaussian.
It is not supplied as an extra theorem assumption.

All reused files are relative links. No shared source, earlier directory,
checker or axioms were changed. Nothing was committed.

1. Main export

SelectedFiniteAlgebraBasis.Over[k,setk,A,S,h,m,n,ab,sb,q,regular]

Inputs:
  k: a commutative set-ring;
  A,S: k-algebras and h:A->S a k-algebra map;
  ab,sb: actual finite k-bases of A and S, of ranks m,n;
  q: a specified prime of A with propositional, decidable membership;
  regular: for each a in A, merely b with a=a*a*b.

No field assumption on k is needed for this export. No field assumption
on the selected ring eA is made anywhere in the relative-basis proof.

theorem : || B.Result ||

The result fields are:
  e, idempotent: e*e=e, outside: not(q(e)), rank,
  basis: TraceBasis of the actual eA-algebra eS, of that rank.

The rings eA and eS are IdempotentFactor's fixed-point subtypes, with
units e and h(e). Their projection maps are constructed ring maps.
The relative scalar map sends a fixed a in eA to h(a) in eS.
No freeness, normal form or finite module presentation is assumed in
the final theorem: all three are constructed from the listed inputs.

The result can have rank zero. Injectivity of h is not required for
the basis theorem; it is preserved by the factor construction when
supplied separately.

2. Exact trace interfaces

For r:B.Result, module Factor[r] exports:

  Relative  = IdempotentAlgebraFactor(...r.e,r.idempotent)
  BasePart  = TraceRetraction.Idempotent[k,setk,A,r.e,r.idempotent]
  Target    = TraceRetraction.Idempotent[k,setk,S,h(r.e),image-idempotent]
  inclusion : k-algebra map BasePart.algebra -> Target.algebra.

Injective[injective].injective-arrow proves that inclusion is injective
when h is injective. This is a proved restriction of injectivity, not
an extra hypothesis on the final factor map.

Field[dec], where dec decides zero-or-unit in k, exports:
  BaseBasis.rank, base-basis;
  TargetBasis.rank, target-basis.
These are actual k-bases of the two exact TraceRetraction algebras.
Their Gaussian construction does not decide whether k is finite.

Thus the result supplies all three bases needed by TraceTransitivity:
the k-bases of eA and eS and the relative eA-basis of eS. Trace or
derivative nondegeneracy is not itself asserted in this directory.

3. Proof and source modules

FiniteAlgebraModulePresentation (reused)
  Uses ab,sb to construct A^n -> S, a finite relation family, and explicit
  coefficients for every kernel vector.

SelectedGaussianConstruction (reused)
  Performs Gaussian elimination over A/q, lifts the finite matrices,
  and kills their finitely many errors using one idempotent outside q.
  Its checked NormalForm has project, section and coefficient maps,
  with retraction, killed relations and corrected differences after
  multiplication by e.

IdempotentVectorMaps.seg
  Restricts each A-linear map to vectors in (eA)^n. Output fixedness
  follows from linearity. Constructs projected vectors, finite-sum
  comparisons, and the translation of weighted equality into equality
  of fixed points.

SelectedNormalFormFactor.seg
  Converts every weighted normal-form identity to the exact identity
  over eA. Projected relation columns and coefficient witnesses remain
  explicit. No quotient field is substituted for eA.

IdempotentAlgebraFactor.seg
  Constructs the eA-algebra eS, including the scalar map, projection
  square and restriction of injectivity.

IdempotentPresentation.seg
  Restricts the supplied A-module presentation to (eA)^n -> eS.
  Surjectivity projects only the supplied finite vectors; every kernel
  witness is projected to a relation witness over eA.

NormalFormModuleBasis.seg
  Private derived variant of GaussianModuleQuotient.seg. The coordinate
  packaging proof is unchanged mathematically: it now receives an exact
  normal form explicitly and works over any set-ring. It never calls
  Gaussian elimination and has no zero-or-unit field parameter. Unique
  coordinates permit elimination of truncated surjectivity. The exact
  source diff is normal-form-variant.diff. No shared source was edited.

SelectedAlgebraBasis.seg
  Applies the constructed selected normal form and the above fixed-point
  presentation. Packages the resulting coordinates as TraceBasis.

SelectedFiniteAlgebraBasis.seg
  Connects FiniteAlgebraModulePresentation to SelectedAlgebraBasis and
  provides the exact trace interfaces described in section 2.

IdempotentFieldBasis.seg
  Independently gives the k-basis of any idempotent factor of an algebra
  with a finite k-basis. Generators are the old basis; relations are the
  n vectors (1-e)*b_j expressed in those coordinates. If e*a=0 then
  (1-e)*a=a, which supplies the complete kernel witness. Existing Gaussian
  quotient coordinates over k then give the actual factor basis.

4. Regression

SelectedBasisRegression uses k=F2, A=F2 x F2, S=F2 with the first
projection A->S, and the prime selected by that projection. Actual
k-bases of A and S feed the full constructed theorem. For every result,
the relative basis and both ordinary field bases have the required
TraceBasis types, and e remains outside the specified prime.

Separate explicit Gaussian factor regressions compute:
  e=0:      rank 0;
  e=(1,0):  rank 1;
  e=1:      rank 2.
The nonzero other component (0,1) is proved killed in the proper factor.

5. Validation

From unit/:
  ./segc sag/etale-field-selected-basis all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-basis/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-basis/All.seg \
    --opens sag/etale-field-selected-basis/etale-field-selected-basis.opens

Fresh All.seg: 8374 declarations, 0 failed, 3.13 s.
segc all: 193 modules, 0 failed, 2.74 s.
Nine owned modules: 318 declarations including 18 open directives.
All 300 named owned declarations have opens specifications, each clean.
Maximum owned declaration time: 0.01 s; maximum definitions opened: 42.
Every fresh check had an external 60-second bound.

Two isolated mutations were rejected without changing working sources:
  replacing the complementary relation multiplier 1-e by e;
  asserting rank 2 for the factor (1,0), whose rank computes to 1.

Logs are /private/tmp/etale-field-selected-basis-{opened,opens,all}.log
and /private/tmp/etale-field-selected-basis-mutation-{complement,rank}.log.

6. Limits

This milestone supplies bases; it does not prove primitive element
existence or derivative invertibility. Those downstream arguments may
now use the constructed relative and ordinary factor bases. The main
input finite k-bases and regularity remain explicit, as intended.
No global decomposition into every field factor is constructed.

The existing All.seg univalence, replacement and surjection parameters
are unchanged. No new axioms or hidden theorem parameters were added.
