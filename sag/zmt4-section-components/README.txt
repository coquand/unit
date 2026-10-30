Actual finite-fibre section components
======================================

1. Result

SectionComponents4 constructs the explicit Pt-indexed section sequence
and identifies the projected native overlap/compatibility errors with
the ACTUAL Cech differential and cochain difference. All witnesses come
from the constructed residual-data/native-chart formulas. There are no
additional mathematical hypotheses.

This directory contains one new source file, 65 declarations. Every older
source is a relative link to zmt4-sections or zmt4-laurent-ring. No earlier
or shared source, checker file or .git was modified; nothing is committed.
All.seg inherits the existing foundational parameters. No new axiom,
resizing assumption or choice principle is introduced.

Parent's FiniteFibreSections4 has already instantiated these components
with SectionErrorRealization4 to export z/w/ideal/J/compatibility witnesses.
This directory supplies component construction and equality; it does not
duplicate the ideal-power/J-witness realization or final ZMT assembly.

2. Precise informal proof and declaration correspondence

left/right name the endpoints of each of the six edges; has-left/right
prove the actual endpoint-chart containment using the existing Le4.

Over[A,setA,D0] imports NativeSectionData4 and NativeSectionErrors4 for
the GIVEN residual data D0. CS0 and CS1 are the root's finite chart
assembly modules for Pt and Ed, respectively, in twist -1.

Chart[E].section k has n defines the native section in chart E: inverse
Z for k=p0 and the explicit affine separator formula for k=p1,p2,p3.
Chart.Part is the constructed degree-(-1) projection to the actual local
chart module. The existing linear-map f-sub lemma proves part-sub:
the degree projection of a native difference is the coefficientwise
difference of its projections.

Restriction[E,F,le].section proves the native section is natural under
restriction. The p0 case uses the constructed coordinate inverse
restriction; the three affine cases use SectionExpression naturality,
already instantiated in NativeSectionData4.Restriction. coefficient
combines this with the native coefficient-preserving restriction theorem;
part transports the coefficient equality through the fixed degree cut.

Point[k].raw n is the native section on its own point chart, and value n
is its actual degree-(-1) local cochain. points n assembles the four local
values and z n is the resulting ACTUAL Pt cochain, with finite support
constructed by ChartFamilyAssembly4. hz0 proves its p0 coefficients are
the exact shifted delta for Z^-1, for EVERY n. It applies the previously
checked ChartInversePart4 normalisation, with no independent assumption
on z at n=0.

Edge[e].raw n is the native RIGHT section minus the LEFT section, both
evaluated in the SAME overlap chart. edge-witness constructs its explicit
I^(n+1)+J witness: ZAffine for the three edges meeting p0; AffineOverlap
in right/left order for e12,e13,e23. These are precisely the signs of the
existing Cech4.d0. Edge.value n projects that native difference and
edge-values assembles its six actual local cochains.

endpoint identifies each projected overlap section with the corresponding
assembled point coefficient by the named restriction part theorem.
d0-value states the six defining differential coefficients once.
edge-equation uses part-sub, endpoint for the two terms, and d0-value to
prove genuine Ed-module equality:
  CS1.assemble(edge-values n) = Cech4.D0(-1)(z n).

Point[k].compat n is the native section_n minus section_0. The affine
compat-witness cases use NativeSectionErrors4.Compatibility. The p0 case
is zero since every section is the same inverse Z; transport of the
native zero witness proves its explicit Witness1. compat-values projects
and assembles these point differences. compat-equation applies part-sub
and coefficient extensionality to give actual Pt-module equality:
  CS0.assemble(compat-values n) = z n - z 0.

All formulas are functions of the natural n. There is no sequence of
chosen local witnesses or representatives.

3. Exact public API

SectionComponents4.Over[A,setA,D0]
  D                  NativeSectionData4.Over[A,setA,D0]
  CS0, CS1           actual Pt/Ed finite chart assembly modules, twist -1
  z n                : CS0.CH.El
  hz0 n m            : val(z n)(p0,m)=old delta0(addE m (1,0,0,0))

  Point[k].C         native chart/projection modules for setPt k
  Point[k].raw n     native section on that chart
  Point[k].compat n  native difference section_n-section_0
  compat-witness n k: native W.Witness 1 (Point[k].compat n)
  compat-values n   : CS0.P.El, actual projected local compatibility values
  compat-equation n : CS0.assemble(compat-values n)=z n-z 0

  Edge[e].C         native chart/projection modules for setEd e
  Edge[e].raw n     native right-section minus left-section in that chart
  edge-witness n e  : native W.Witness (suc(toB n)) (Edge[e].raw n)
  edge-values n     : CS1.P.El, actual projected local overlap errors
  edge-equation n   : CS1.assemble(edge-values n)=Cech4.D0(-1)(z n)

The native W.Witness records are the untruncated witnesses of
SectionsErrorWitness: an explicit ideal-power part, its recursive witness
tree, native coefficients of the original homogeneous J equations, and
the exact native ring remainder equation. SectionErrorRealization4 maps
these records into the actual cochain ideal/J witnesses.

4. Validation

From unit:
  timeout 55 ./segc sag/zmt4-section-components all
From sag/zmt4-section-components with the built checker called seg:
  timeout 55 seg All.seg --opened
  timeout 55 seg All.seg --opens zmt4-section-components.opens

Recorded results:
  207 modules, 0 failed.
  Fresh All.seg: 11898 declarations, 0 failed, approximately 6.3 s.
  65 new declarations; every one audited with --opened and --opens.
  At most 33 definitions opened and 0.05 s per new declaration.
  All 65 profiles report "nothing else opened".

The profiles explicitly contain finite chart assembly, coefficient/degree
cut definitions, endpoint maps, native chart ring carriers and operation
aliases, and actual Cech/submodule operation aliases used at the final
module equalities. They do not unfold a separator or native overlap proof
to obtain a new equality.

Two isolated temporary mutation copies were rejected: reversing the
native overlap difference and reversing the native compatibility
difference. The native witness declarations and actual cochain equalities
detected each wrong sign. The live sources were never mutated while the
other agents used this API.
