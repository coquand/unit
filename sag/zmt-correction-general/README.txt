zmt-correction-general: all-dimension section/Rees interface transport
====================================================================

Public theorem
--------------
GenericCorrectedSections.Over[K0,A,setA,cfn,extra,D0].correction

Here m = extra+2, nvar = suc m, and D0 is ResidualAlgebra.Residual[A,setA,m].
The ONLY inputs are CFN set-ring data and the residual finite-fibre data.
S = GenericFiniteFibreSections.Over[A,setA,m,D0] supplies the actual native
section construction; ST=S.ST supplies its original homogeneous equations.
J is GenericReesChart.Over[A,setA,nvar,D0.t,D0.b,m,ST.P,ST.e,S.hpC].
J0 and J1 are J.At[-1,rank1/2].Q, with actual GenericCech modules.

Corrected = (zz:J0.Target.M) *
 (J1.InJ(N.d zz) * J0.IJ 1 (J0.ML.msub zz (S.z zero))).
The theorem is Trunc[Corrected]. The native dimension is EXACTLY suc m;
there are no manually transported polynomial, cochain, exponent, ideal or
source-family components in this result.

hz0 is the exact normalization of S.z zero on the newest-coordinate Z chart:
its coefficient at v is the native delta0 coefficient at v+axis(Z).
This is an exact statement about the original section. The corrected
section is congruent to that section modulo I+J, as stated above.

Why transport is needed
-----------------------
GenericReesFromSections is parameterized by nvar=extra+3, while actual
finite-fibre sections and affine extraction use nvar=suc(extra+2).
GenericCorrectedSections.coordinate-count proves the equality by recursion
on extra. GenericCorrectionTransport.Package n quantifies over the ENTIRE
correction method: polynomials, term homogeneity, actual chart modules,
section sequences, ideal trees, J remainders and compatibility witnesses.
Its base method is the already constructed Rees theorem; transported uses
ONE path substitution of this whole package. This makes the final native
chart interface agree definitionally with the section/extraction APIs.
The only additional local transport equates the two existing Nat-to-BaseNat
conversion functions in the explicit ideal-power witness depth.

Scope/foundations
-----------------
The theorem holds for ALL extra, not only the five-coordinate regression.
Thus it handles every affine arity m>=2 through this parameterization.
Lower arities still use the external padding/export track. No new axioms,
choice principles, kernel hypotheses, resolution inputs, section formulas
or local exactness assumptions are introduced. This is an integration
wrapper over constructed prior theorems. All imports are relative links;
no earlier/shared/checker/git file was changed or committed.

Files
-----
GenericCorrectionTransport.seg: 30 declarations, generic dimension package.
GenericCorrectedSections.seg: 30 declarations, residual-data-only theorem
and exact original-section normalization.
All.seg: reused dependency import order plus these two new modules.
zmt-correction-general.opens: complete opening spec for all 60 declarations.
