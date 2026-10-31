Selected coordinate generation
==============================

This directory proves the coordinate-to-generation step and its concrete
monic-quotient corner adapter. It does not construct the tensor separator
or prove the coordinate identities; those identities are explicit inputs
supplied by etale-field-tensor-separation.

CoordinateGeneration.Over[A,setA,S,r,basis,q,coordinate].theorem regular
returns merely Result. Here S is an A-algebra, basis is an actual finite
A-basis, q is a decidable proper prime of S, and coordinate means
 h(lambda_j(s)) = h(lambda_j(1))*s.
Expanding 1 supplies an actual j for which a=lambda_j(1) lies outside q.
From a=a^2*b, the proof constructs the idempotent e=a*b outside q and
actual preimages b*lambda_j(s), with h(preimage(s))=h(e)*s. It avoids a
rank-one argument. The regular witness is used only under truncation.

MonicRepresentatives.Over[k,setk,lower] constructs an ACTUAL coefficient
list for every element of Q=k[T]/(monic lower), from its canonical
remainder coordinates. Map[S,h].value proves its Horner value at h(T)
equals h(a). Two existing opaque expansion definitions are exposed
locally for named definitional boundary lemmas, then locked again.

MonicCoordinateGeneration.Over[k,setk,lower,S,h,e,he,q,outside-e]
uses Q above, h:Q->S, and the selected factor e of Q. Its derived Part
is exactly IdempotentAlgebraFactor, so eS/eQ have the same carriers and
operations as the selected basis development. At[r,basis,coordinate]
takes an actual eQ-basis of eS and the coordinate identities there.
Its theorem regularQ returns merely a Result containing:
- value in S, value^2=value, value outside q;
- h(e)*value=value (the new factor refines the old one);
- representative:S->List k, with actual lists;
- value*(s-Horner_(h(T))(representative(s)))=0 for every s.

Regularity of eQ is constructed from regularity of Q. The prime of eS
is the pullback of q along its nonunital inclusion, whose unit h(e) lies
outside q. Every original s is first projected into eS; its resulting
coefficient in eQ is viewed in Q and given its polynomial representative.
No injectivity, field, separability or choice assumption is needed in
this coordinate argument. A finite family of representatives is obtained
by applying the constructed function to the supplied ambient basis.

Regression and validation

CoordinateGenerationRegression checks the identity extension over F2 x F2
and the genuinely nontrivial first factor of its concrete minimal quotient.
The latter has its actual rank-one relative basis, constructs the selected
idempotent, verifies that it is the first-factor unit, constructs a
polynomial representative for the generator and runs the truncated theorem
with the previously constructed regularity. No relative basis is assumed
in this regression.

Fresh All.seg --opened: 9430 declarations, 0 failed, 4.17 seconds.
./segc sag/etale-field-coordinate-generation all: 221 modules, 0 failed,
3.68 seconds. There are 193 owned declarations in four proof files.
All 193 are in coordinate-generation.opens and report nothing else opened.
Every owned declaration takes at most 0.02 seconds. Generic proofs open
at most 24 definitions; the nontrivial corner regression opens at most 58,
mainly the nested fixed-point carrier and concrete monic quotient aliases.

Owned proof files: CoordinateGeneration.seg, MonicRepresentatives.seg,
MonicCoordinateGeneration.seg, CoordinateGenerationRegression.seg.
All other proof files are relative links. No shared file, checker or
previous development was edited. No new axioms; All.seg retains the
existing univalence/replacement/surjection parameters. Nothing committed.
