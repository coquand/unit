Finite basis of the full tensor algebra
======================================
TensorFieldBasis.Over[k,setk].At[S,D,cp,n,b] constructs a k-basis of
D=S tensor_k S from its actual coproduct and a supplied rank-n basis of S.
The rank is FiniteProduct.size n n. The final basis belongs to the exact
original D algebra, with its original scalar map.

The proof packages TensorBasisConstruct's right-S basis and applies
FiniteBasisComposition. coordinate-pair identifies the paired coordinates;
tensor-expansion retains the original right-S reconstruction formula.
No field, reducedness or diagonal-certificate hypothesis is needed.
There are no new axioms, checker changes or changes to shared source.
Reused source is linked relatively. Nothing was committed.

Regression: the actual tensor coproduct of Z/4Z with itself, rank 1,
including reconstruction and paired coordinates.
Validation: fresh All.seg 7762 declarations, 0 failed, 3.02 s;
segc all 183 modules, 0 failed, 2.64 s. The 37 owned declarations include
33 named declarations; all 33 have clean --opens audits. Maximum owned
check time 0.06 s and maximum 26 definitions opened.

This is a basis wrapper. It does not construct the separator polynomial,
choose its scalar parameter, or prove primitive generation.
