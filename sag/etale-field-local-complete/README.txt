The completed field theorem in the local lifting argument
=======================================================

1. Endpoint

LocalFieldComplete.Over[the existing local setup,prop-m]
.GivenInverse[N,v,relation].Field[field,fp,unique,prime,prime-map]
exports:
- selected-data : || SelectedFlatLocal.SelectedData ||;
- theorem : || FlatLocalStatement.Conclusion ||.

The latter gives an element outside the specified prime q and an actual
localisation of E at that element which is standard etale and etale in
the existing square-zero lifting definition (with finite presentation).
The endpoint no longer takes a basis or a SelectedFactorStatement.Selected
certificate for the special fibre.

The exact special fibre is
  k = A/m,
  C = (B/mB)[1/s],
using QuotientFibre and PowerLocalization, through the existing
SelectedLocalLift construction. The field argument is applied to this
exact C algebra over this exact k; no quotient-identification parameter
or assumed injection B/mB -> C occurs.

2. Hypotheses which remain explicit

The outer parameters are exactly the existing SelectedLocalLift local
setup, including:
- The local base A, ideal predicate m with ideal laws, zero-or-unit
  decision, the stated radical unit law, and propositional membership.
- E as an A-algebra with an actual finite presentation and the checked
  finite-relation flatness property.
- The specified prime predicate q of E, its ideal/prime/proper/decision
  laws, and containment of the image of m.
- ZMT data B -> E over A: a nonempty finite spanning family bs of B with
  truncated coordinates, s in B with j(s)-1 in mE, and the explicit
  denominator-clearing representation of each element of E.

GivenInverse supplies N,v and
  s^N*(1-s*v) in mB
in the actual QuotientFibre.InIE sense. Field supplies:
- the discrete nonzero Field record for the exact quotient k;
- fp:Presentations.FP C and unique:FormallyEtale.Unique C;
- a specified decidable proper prime of C;
- prime-map: q(j(b)) implies prime(eta(b)), where eta:B -> C is the
  actual quotient followed by the localisation map.

This wrapper does not construct these local inputs. In particular it is
not yet a theorem deriving the local conclusion directly from arbitrary
A,E, finite presentation, flatness and unramifiedness alone. Constructing
the ZMT data, quasiinverse, exact C's FP/Unique, and compatible prime from
the original local hypotheses remains separate integration work. The
field record can be obtained from the existing LocalResidueField theorem
when its properness/local hypotheses are supplied, as in the regression.

3. Proof and truncation

UnramifiedFieldSelected applied to C constructs merely a Certificate
containing a dimension, an actual basis and the exact selected separable
monogenic factor. The new wrapper binds this truncation into the
propositional selected-data target of the old lifting bridge. For each
certificate it instantiates SelectedLocalLift.Given with the constructed
basis and selected factor. It then applies the existing local theorem.

No basis, primitive element, simple-root equation, tensor diagonal or
field-case principle is added as a hidden theorem parameter. The finite
representations and all powers of s used by the old lifting proof are
retained unchanged. The output remains truncated throughout.

4. Actual regression

LocalFieldCompleteRegression uses A=E=F2, B=F2 x F2, s=(1,0), and the
first projection B -> E. It reuses the existing quotient/localisation
maps and their scalar retraction. From that retraction it constructs the
empty presentation of the exact C and proves Unique directly: every
k-algebra map out of C is determined by scalars. LocalResidueField gives
the discrete field record of the exact k. The compatible prime and
quasiinverse relation are explicit.

The new wrapper then constructs a basis and selected factor and runs
both exported endpoints. The previous handwritten basis and selected
certificate are not supplied to the new theorem. The regression retains
the nonzero class of (0,1) in B/mB and proves it is zero after localisation,
so an injection of the special fibre into its localisation is unavailable.

5. Validation

Fresh All.seg: 21221 declarations, 0 failed, 11.72 s.
./segc sag/etale-field-local-complete all:
474 modules, 0 failed, 10.70 s.
90 declarations are owned by this directory, including 4 opens. The
86 named declarations all have exact entries in
etale-field-local-complete.opens; each reports "nothing else opened".
Each owned declaration takes at most 0.03 s and opens at most 27 distinct
definitions. The inherited proof tree accounts for the remaining counts.

Two isolated mutations failed: erasing the given exponent N from the
quasiinverse relation, and falsely claiming the killed localisation class
is 1 instead of 0. The working proof files were not mutated.

From unit/:
  ./segc sag/etale-field-local-complete all
Fresh checker from this directory:
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opened
  ../../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg --opens etale-field-local-complete.opens

All reused source files are relative links. All.seg merges the completed
field and local-lift trees in dependency order, respecting lexical module
names. No shared-file changes, checker edits or new axioms were made.
The existing univalence, images and surjection parameters are inherited.
The checking server is stopped. Nothing is committed.
