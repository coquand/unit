Finite monic coefficient collection
==================================

FiniteMonicCoefficientFamily.Over[k,setk,S,n,basis].theorem merely gives
Data containing:
- a lower coefficient list for a monic annihilator of every basis vector;
- the global root equations, with no selected idempotent;
- count and coefficient:Fin count->k;
- an actual location of every occurrence of every lower coefficient.

The finite basis gives spanning witnesses directly. FiniteSpanIntegral
constructs the monic equations by the determinant trick. Only the n
resulting witnesses are selected, inside truncation. There is no field,
reducedness, trace or supplied-annihilator hypothesis in this theorem.

CoefficientCollection flattens the lists by finite concatenation. It
retains repetitions, handles empty lists and an empty family, and records
Locations recursively: a finite index and its equality for each head,
followed by locations for the tail. No equality decision on coefficients
is needed. The leading coefficient 1 is implicit in the monic convention
and therefore does not need a location in the collected family.

Given[d].ordinary-root supplies the ordinary Horner root of
SelectedFactorStatement.monic(d.lower i). Given[d].Lift takes:
 K0, setK0, inclusion:K0->k,
 preimages:Fin d.count->K0,
 image-law:inclusion(preimages j)=d.coefficient j.
It constructs actual lower lists over K0, their coefficient-image
equalities, the restricted K0-algebra, and the corresponding root
equations. roots has exactly the MonicBasisUniversal.Values convention
used by IteratedMonicBasis.Roots and SmallFieldBranch.Given;
ordinary-lifted-root gives the ordinary Horner version as well.

Integration with the bounded coefficient-field dichotomy:
inside d's truncation, apply FiniteCoefficientField to d.count and
d.coefficient. If it returns K0, instantiate Lift with K0.ring, K0.set,
K0.inclusion, K0.coefficient and K0.coefficient-image. The resulting
lower and roots are the inputs of SmallFieldBranch.Coefficients.Given.
The dichotomy and the primitive-element theorem are not reimplemented
in this helper directory.

Regression and validation

MonicCoefficientRegression uses F2 x F2. Both basis vectors use T^2+T;
the four coefficient occurrences, including repeated 0 and 1, are
collected. Lifting through the identity coefficient map reconstructs
both lists by computation and checks both root equations. Empty families
and nonempty families of empty lists have zero coefficients. The general
determinant-trick existence theorem is also applied to the actual basis.

Fresh All.seg --opened: 9334 declarations, 0 failed, 4.03 seconds.
./segc sag/etale-field-monic-coefficients all: 219 modules, 0 failed,
3.61 seconds. All 115 owned declarations are listed in
monic-coefficients.opens and report nothing else opened. Every owned
declaration takes at most 0.01 seconds. Generic proofs open at most 7
definitions; computed regressions at most 29.

Owned files: CoefficientCollection.seg, FiniteMonicCoefficientFamily.seg,
MonicCoefficientRegression.seg. All other proof files are relative links.
No shared/checker files or earlier developments were changed; no new
axioms; All.seg retains the existing univalence/replacement/surjection
parameters. Nothing committed.
