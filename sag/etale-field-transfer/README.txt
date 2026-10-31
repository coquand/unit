General flatness transfer from formal unramifiedness
====================================================

1. Checked theorem

FlatDiagonalTransfer.Over[R,setR].At[S,T,u,fp,unique,flat].theorem

R is a commutative set-ring. S and T are R-algebras, u : S -> T is an
R-algebra map, fp says S is merely finitely presented, unique is precisely
FormallyEtale.Over[R,setR].Unique S (uniqueness over square-zero quotients),
and flat says T is R-flat, in FlatRelations' finite-relations sense.
The conclusion is that T is flat over S through u.

There is no field hypothesis, standard presentation, lifting-existence
hypothesis, or finite-presentation hypothesis on T. There is no ZMT input.
No new axiom or shared/checker change is made. The univalence, replacement
and surjection parameters of All.seg are inherited unchanged.

2. Construction

FlatAveraging: for a flat extension S -> D, maps T -> D -> T and an element
e with mu(e)=1 and e*left(s)=e*right(u(s)), the map t |-> e*right(t) is an
S-linear section. FlatRetraction gives S-flatness of T. Idempotence of e
is not required at this step.

FlatCocone: a record holds a constructed extension S -> D <- T, its
flatness over S, maps out for any pair, and the two beta laws. A full
uniqueness theorem for maps out is unnecessary. Polynomial extension and
simultaneous principal quotient preserve this record. They use the
already checked FlatPolynomialBaseChange and FlatPrincipalQuotient.

FlatQuotientPresentation: the base R has the empty presentation, and
quotienting a presented algebra by the value of one equation gives the
presentation with that equation added. The proof uses effective principal
quotients and their actual universal maps, not an assumed comparison.

FlatPresentedCocone: recursively adjoin n polynomial variables, then
quotient by the finite equation list. This constructs the flat extension
for arbitrary T. PresentationComparison identifies its source with the
given S, and FlatSourceIso transports flatness.

FlatDiagonalTransfer: reuse the checked diagonal certificate from
../etale-field-diagonal. The diagonal coproduct maps to the constructed
extension using (left,right*u). Coproduct uniqueness compares its composite
with mu to u times the original multiplication map. The image of epsilon
therefore has image 1 and equalizes all source elements. Apply averaging.
Chosen presentations and diagonal elements stay inside truncations;
flatness is constructed one finite relation at a time.

3. Files and checking

Six owned proof files: FlatAveraging, FlatCocone,
FlatQuotientPresentation, FlatPresentedCocone, FlatDiagonalTransfer,
FieldTransferRegression. All other .seg files are relative links.

  ./segc sag/etale-field-transfer all
  ./segc sag/etale-field-transfer check FlatDiagonalTransfer

The built checker may also be run on All.seg with --opened or with
--opens sag/etale-field-transfer/etale-field-transfer.opens.

Fresh validation (31 October 2026):
  All.seg: 7532 declarations, 0 failed, 2.81 s.
  segc all: 172 modules, 0 failed, 2.23 s.
  263 owned declarations; all 263 are covered by the .opens specification.
  --opened: each owned declaration rounds to 0.00 s; at most 28 definitions
  opened. The audit lists inherited quotient/evaluation implementation
  aliases explicitly, including map, choose, induction, include and ring.
  The mathematical boundary statements are the named beta laws; comparison
  with the older APIs sometimes opens these concrete implementation aliases.

Regressions:
  * Empty presentation, over any commutative set-ring R and arbitrary
    R-flat T: the general transfer theorem applies to R -> T.
  * The constructed standard algebra for X^2-X over Z/4Z, evaluated at
    zero: apply the NEW general theorem, and then the flat-kernel theorem
    to the nonzero distinguished root. This reuses the earlier construction
    and nonzero proof, but does not use its old standard-transfer proof.
  * Mutating the polynomial extension to send the variable to zero instead
    of its required image was rejected. Replacing the averaging element
    with zero was rejected. Both were restored and checked again.

4. Exact scope

This completes the general transfer dependency of the proposed field
regularity argument. It does not prove finite dimensionality, primitive
elements, the residual coefficient bridge, or the unconditional local
etale statement. Those are separate developments.

The constructed target satisfies the maps-out existence and beta laws
needed here; it is not packaged as a coproduct with uniqueness. No
downstream step uses such a uniqueness claim. The diagonal source itself
is the genuine checked coproduct from Tensor.

Nothing is committed.
