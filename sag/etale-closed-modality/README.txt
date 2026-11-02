SUPERSEDED (2 November 2026, later): for the field route the right O is
"1 = 0 in k". Every conclusion then holds when O does, so Cl X = Trunc X
and the closed modality collapses to a merely given decision; "nonzero"
becomes "unit". This is now built in the shared files (see
etale-field-regularity/README.txt, etale-field-fibre/README.txt).
LocalResidueFieldClosed was removed; FieldLeadingClosed and
ClosedModality remain only as the record of the pilot.

Closed-modality route for hit-or-split (pilot, 2 November 2026)
==============================================================

Problem. In hit-or-split the local ring R = A_M need not have pR proper,
and properness cannot be decided in advance. LocalResidueField.decide
descends the zero-or-unit decision to Q = R/I only because it is a
proposition, which needs 1 /= 0 in Q. That is intrinsic: if 1 in I then
Q = 0 and both alternatives hold.

Idea. Fix the proposition O to which the degenerate case exits
(in the cover, O = a split). Work in the closed modality
Cl X = Trunc (O + X). Cl X is always a proposition, so the decision
descends; "1 /= 0" becomes "1 = 0 -> O". Every goal of the field route
is a truncated proposition, so it can be made Cl-valued (O-modal).

Files (new; everything else links to etale-field-fibre's closure):
  ClosedModality.seg          Cl, ret, exit, Modal, rec, bind, map;
                              from-trunc, lift: decision-free lemmas
                              Trunc X -> Trunc Y lift to Cl X -> Cl Y.
  LocalResidueFieldClosed.seg decide : (x : Q) -> Cl (Decision x) with
                              no properness; nonzero : 1 = 0 -> O.
                              Proper: O = Empty gives back
                              LocalResidueField's decision.
  FieldLeadingClosed.seg      pilot conversion of FieldLeading
                              (scan/result/leading Cl-valued).

Check: ./segc sag/etale-closed-modality all  (from unit/)
  13954+ declarations, 0 failed, about 5.7 s fresh.

Measured scope of the full conversion (closure of
UnramifiedFieldFiniteGeneral: 168 files, 14.2k lines): only 11 files,
641 lines, take a decision or nonzero parameter (MonomialDifference,
FieldFlat, MonomialNormalize, MonomialFamily, NagataReduction,
ZeroDimensionalRelation, NagataSparse, PrincipalRegularity,
UnramifiedFieldFiniteGeneral, UnramifiedFieldRegular,
ZeroDimensionalFinite), plus the Cl-valued induction in
GeneratedFiniteInduction (57 lines). The rest lifts by
ClosedModality.lift. Data built by decisions (MonomialNormalize.filter,
SparseData.nonzero) becomes one Cl-valued induction producing the data
with its properties; nonzero fields become "= 0 -> O".

Open points.
- DONE for FieldLeading (alternative 1): etale-field-finite/FieldLeading
  now has the decision-free notions (Zero, Leading, Result, Normalize)
  in Over[A] and the old scan in Over[A].Given[dec]; callers updated
  (MonogenicFinite, perdry KroneckerTest/Theorem43), inventory renamed;
  all 12 linking directories check. FieldLeadingClosed uses the shared
  notions. The same split is to be done in the other files.
- FieldLeadingClosed.Given.scan-suc opens Cl/Trunc (3 definitions,
  0.00 s) when comparing M.bind's argument with dec's type: probably
  the alias M seen from the nested module Given. Not yet diagnosed.
- ClosedModality is at one level l; the cover's goal Trunc(Hit+Split)
  is at l+, so the final step needs a two-level rec.
