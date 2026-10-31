Tensor separation and relative coordinate identities
===================================================

1. Checked statements

TensorContraction.Over[k,setk,S,D,cp,n,basis,T,j,f] takes commutative
set-algebras over k, an actual coproduct D=S tensor_k S, a finite k-basis
of S, an algebra map j:S->T, and a k-linear map f:S->T. It constructs
  map(left(a)*right(b)) = f(a)*j(b).
The construction uses the checked right-S coordinates of D. It proves
addition, scalar multiplication and the displayed pure-tensor formula.
Balanced[z,balanced] assumes f(z*a)=j(z)*f(a); its kills theorem states
that contraction vanishes on every multiple of Delta z=left(z)-right(z).

TensorSeparatingElement.Over[k,setk,S,D,cp,n,basis,epsilon,z,w,inverse]
additionally takes a DiagonalCertificate.Witness epsilon and the equation
  Delta z * w = 1 - epsilon.
The diagonal equalisation gives epsilon*Delta a=0 for every a, and hence
  Delta a = Delta z * (w*Delta a).
Balanced[T,j,f,balanced].theorem consequently proves
  f(a) = f(1)*j(a)
for every k-linear f satisfying the z-balance equation. There is no field,
reducedness, nonzero-ring or separability hypothesis beyond the supplied
diagonal certificate and separating equation.

TensorRelativeCoordinates.Over[the same separation inputs]
.Relative[A,T,h,p].Basis[r,basis,t,contains]
takes algebra maps h:A->T and p:S->T, an actual rank-r A-basis of T,
and contains:p(z)=h(t). Its theorem accepts merely-surjectivity of p and
proves, for every basis coordinate lambda_i and b in T,
  h(lambda_i(b)) = h(lambda_i(1))*b.
It applies the separation theorem to the k-linear composite
  S --p--> T --lambda_i--> A --h--> T.
Surjectivity is eliminated into the propositional equality, without
choosing representatives globally. No injectivity of h or p is assumed.

2. Scope and downstream dependency

This directory constructs the contraction and the displayed coordinate
identities. It does not construct z,w or their separating equation, and
it does not supply the relative basis. The diagonal and finite k-basis
are explicit inputs; their constructions live in earlier developments.
The coordinate-to-generation argument and selection of the separating
polynomial value are separate bridges. This directory does not claim the
full primitive-element or residue-field theorem.

The tensor is the actual algebra coproduct, not a postulated bilinear
formalism. TensorBasisConstruct supplies its finite coordinate expansion.
The tests below execute that construction as well.

3. Regressions

TensorSeparationRegression constructs the actual tensor of the base
algebra over any commutative set-ring. Its diagonal idempotent is 1, so
w=0 satisfies the separating equation. The map f is multiplication by
an arbitrary b; the relative projection is the identity with the actual
rank-one base basis. Both the contraction/separation theorem and the
relative coordinate theorem are exercised.

The explicit specialization is Z/4Z, with b=3 and the nilpotent z=2.
The contraction on pure tensors and the resulting multiplication identity
are checked, together with 2*2=0. This regression deliberately covers a
nonreduced coefficient ring. It does not test a nonzero off-diagonal
factor; that case belongs to the separator-value assembly.

4. Fresh validation

Fresh All.seg: 7823 declarations, 0 failed, 3.03 s.
./segc sag/etale-field-tensor-separation all:
182 modules, 0 failed, 2.69 s.
The four owned modules contain 137 declarations, including 8 opens.
All 129 named declarations appear in etale-field-tensor-separation.opens;
every entry reports "nothing else opened". At most 13 distinct
definitions open. Every new declaration takes at most 0.06 s. The
contraction proof was split into named left-pure and expanded equalities;
this reduced the full TensorContraction module time from 0.43 s to 0.07 s,
without changing its input or output. The previous single left-action
proof took 0.40 s; its new named steps each take at most 0.02 s.

Two isolated mutations were rejected: replacing Delta z by the sum of
its two tensor embeddings, and dropping the factor f(1) from the final
balanced-map identity. The original mathematical files were unchanged.
Logs are /private/tmp/etale-field-tensor-separation-{opened,opens,all}.log
and the corresponding mutation-sign/mutation-factor logs.

From unit/:
  ./segc sag/etale-field-tensor-separation all
Fresh checker from this directory:
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opened
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opens etale-field-tensor-separation.opens

The checking server is stopped. Reused files are relative links. No new
axioms, checker changes, shared-source edits or changes to earlier
mathematical developments were made. The reused univalence, images and
surjection parameters of All.seg remain explicit. Nothing is committed.
