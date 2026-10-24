SAG Section 5
=============

Worker A's development, with Worker B's Section 5.3 checked by Section5.seg.
Section 5.6 is checked. The qualifications on hypotheses and pushouts are below.

Definitions (Schemes.seg)
------------------------
Schemes[l].Over[R,setR].Chart[X] consists of:
  presentation : a finite presentation p;
  map : Solutions(p,R) -> X;
  embedding : every fibre of map is a proposition;
  open-image : every truncated fibre is an open proposition.

Cover[X] consists of a natural number, that many charts, and the assertion
that every x merely belongs to a chart image. Scheme X = ||Cover[X]||.
Both Cover[X] and Scheme X live in U l. The type of all small schemes
is the expected larger type (X : U l) * Scheme X in U l+.

The theorem set proves Scheme X -> isSet X. X is not assumed to be a set
in the definition. An embedding from a set makes all equalities starting
at an image point propositions; the proof uses local Hedberg, then cover
and propositional-truncation elimination.

Small affine witnesses (SmallAffine.seg)
---------------------------------------
Witness X = (p : Presentation) * Equiv X (Solutions(p,R)), in U l.
Its truncation is logically equivalent to the existing large Affine X.
The forward implication flattens affine and finite-presentation
truncations. The converse uses the already constructed presented algebra.
Neither direction needs Loc, SQC or Z-choice.

Subtype formulation (SchemeSubtype.seg)
---------------------------------------
An actual equivalence of propositions identifies Scheme X with SAG's
definition: merely a finite cover by open subtypes with affine total spaces.
The latter witness is large. Finite choice of small presentation witnesses
converts it to the small chart form; it does not choose presentations
over all points of X.

Finite-cover flattening (SchemeCover.seg)
-----------------------------------------
If finitely many open subtypes cover X and their total spaces are schemes,
then X is a scheme. Finite choice chooses their affine covers inside the
truncated goal, SchemeFinite concatenates them, and open transitivity
makes the inner chart images open in X.

This module takes SAGAxioms[l,l].Assumptions through the existing
Transitivity.sigma theorem. There is no separate Z-choice application
or use of 4.2.7 in this construction.

Basic introductions and regressions
-----------------------------------
SchemeBasics supplies the empty scheme, affine schemes, presentation
solution schemes, and invariance under equivalence.
SchemeExamples checks smallness directly, including a well-typed
application of level-l Z-choice to Cover[Ys x]; the empty subtype
round trip; the empty-family flattening case; and two rejected attempts
to omit an embedding or cover an inhabited type with no charts.

5.1.3: local choice (SchemeChoiceHelpers, SchemeChoice)
-----------------------------------------------------
Given pointwise mere inhabitants of B:X->U l and a scheme X, there
merely exists a finite affine open cover with sections of B on each
chart. theorem-on-images gives sections on each open image.

For an actual original cover, FromCover.refinement retains per-chart
Z-choice data: finitely many functions generating the unit ideal,
sections on their principal opens, and equivalences identifying the
refined chart images with those opens. Localizations are finitely
presented, and their affine witnesses are converted to small presentation
codes. Finite choice and concatenation produce the resulting cover.
The statement is mere existence; no presentation or section is selected
globally over X. Only level-l Z-choice is used.

5.2.1: specialisation (SchemeSpecialisation)
-------------------------------------------
Specialisation in a scheme is equivalent to double-negated equality.
Choose a chart containing x inside the proposition-valued goal.
Specialisation puts y in that chart too, and open transitivity extends
its open subtypes to X. Apply the affine result there. The reverse
implication is the existing theorem for any type.

This formal proof uses Loc, SQC and Z-choice through open transitivity,
where the paper labels 5.2.1 Loc/SQC. The local-choice construction also
takes the full bundle, whereas the paper labels 5.1.3 Z-choice.
The weaker hypothesis lists have not been established here.

5.4: subschemes (SchemeAffineOpen, SchemeSubtypes)
------------------------------------------------
Subscheme packages both proposition-valuedness of the family and
schemehood of its total space. Open and closed subtypes of schemes
satisfy it.
For an open subtype of an affine type, 4.2.7 gives a finite principal-open
cover; each principal open is affine by its localization. For a general
scheme, restrict its affine charts to the subtype. For a closed subtype
the restricted charts are affine by 4.1.4; for an open subtype they are
schemes by the affine case. Finite-cover flattening finishes.

5.5: equality types (AffineEquality, SchemeEquality)
---------------------------------------------------
Affine equality is a finite system of coordinate equations.
Every closed proposition is affine: the constants of its equations
give a presentation with zero variables. Thus 5.5.1, including affine
equality and the closed diagonal, needs no geometric axiom.

For general X, choose an affine chart containing x. Its membership
predicate U(y) is an open proposition and therefore a scheme. Over it,
the equality (x,ux)=(y,u) in the chart is closed. This closed subtype
is equivalent to x=y; an equality transports ux to y to give the inverse.
There is no assumption that y belongs to the chosen chart.

SchemeResultsExamples checks true/empty subtypes and the empty equality
of zero and one in the affine line. SchemeChoiceExamples covers empty
schemes, sections of Top, and impossibility of an empty-family section
cover of Top. Four new invalid assertions are rejected.

5.6: dependent sums and their corollaries
----------------------------------------
SchemeSums.theorem proves Scheme X -> ((x:X) -> Scheme(Y x)) ->
Scheme(Σx:X. Y x), for arbitrary small families Y.

There are two separate bounds. First, after locally choosing presentation
witnesses over an affine base, SchemeBounded bounds their variable counts.
PresentationPadding embeds each solution set in R^N by constraining all
added coordinates to zero. The equation count need not be bounded.
AffineSigma identifies the total space with a closed subtype of X × R^N
and applies 4.1.4. SchemeAffineSums combines these local results; it claims
schemehood, not affineness, for an arbitrary family of affine fibres.

Second, SchemeChoice locally chooses actual finite covers of scheme
fibres. SchemeBounded bounds their chart counts over each affine base
chart. SchemeCoverPadding extends every cover to the same size using
empty affine charts, presented by 1=0. For each fixed chart index the
fibres are now affine, so SchemeAffineSums applies. Finite-cover flattening
and CoverSigma assemble the result. All choices are made under truncation
and eliminated into schemehood; level-l Z-choice suffices.

SchemeFamilies.Over[R,setR,axioms].At[X,scheme] exports:
- theorem-5-6-2: an equivalence between maps of schemes into X and
  X-indexed families of schemes, using actual fibres and total spaces;
- Subtype[Y,prop].theorem-5-6-3: a proposition-valued family is a subscheme
  exactly when its values are schemes;
- Family[Y].equivalence: schemehood of the total space is equivalent to
  pointwise schemehood, for a scheme base X.
FamilyClassification proves the underlying map/family classification
using univalence, with no geometric axiom.

SchemePullbacks.theorem proves 5.6.4 for the usual pullback
Σx:X. Σy:Y. f x = g y. It uses dependent sums and scheme-valued equality.
It also exports product and fibre closure.

FamilyExamples tests a map with two-point fibres, the actual map round
trip, and the empty subscheme. SchemeSumExamples tests zero-constrained
padding, empty padded covers, empty sums, and a scheme pullback that has
no points. Three additional invalid assertions are rejected.

Ownership and scope
-------------------
Worker A owns these files. Imported dependencies are read-only symlinks.
Worker B owns the gluing construction in a separate directory and reuses
the existing effective quotient in projective/Quotient.seg.

Worker B's gluing construction is now checked in ../gluing, and
Section5.seg checks it together with every shared-interface file here.
Its universal property is for maps into sets B : U l; the arbitrary-type
and larger-universe target versions are not claimed.
There are no checker changes or new foundational axioms. Nothing is committed.

Check from this directory with the seg executable:
  seg All.seg
This direct check uses neither --only nor a checking server.
For the combined shared-interface and gluing check:
  seg Section5.seg
