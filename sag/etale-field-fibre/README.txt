Actual residue fields and finite quotient fibres
===============================================

1. Main result

FiniteSpecialFibre.Over[R,setR,I,propI,proper,local,E].theorem fp unique
  : || QuotientFibre.Over[R,setR,I,propI,E].Finite ||

Inputs:
  R       any commutative set-ring;
  I       an ideal with proposition-valued membership;
  proper  1 is not in I;
  local   for every a:R, either a is in I or a is invertible;
  E       an R-algebra;
  fp      merely a finite algebra presentation of E;
  unique  formal unramifiedness, uniqueness of square-zero lifting.

Conclusion: the actual E/IE is merely finite as a module over the actual
R/I, with precisely the quotient constructions and ModuleFinite interface
used by zmt-descent/QuotientFibre. The map elementwise also exports the
elementwise FiniteFibre required by FiniteFibreCertificates.

There is no ZMT, CFN, field-extension, trace, basis, or residue-field
structure assumption. The field theorem supplies finiteness before ZMT
is applied. Some reused files also contain conditional ZMT theorems;
this proof does not invoke their UniversalZMT or CFNZMT parameters.

2. Construction

LocalResidueField.Over[R,I,propI,proper,local]:
  Q.ring, Q.set    the effective R/I;
  nonzero         1 != 0 in R/I;
  decide          every quotient element is zero or explicitly invertible.

The decision descends through the quotient because its two alternatives
are propositions and disjoint. No representative-selection function is
assumed or extracted from truncation.

QuotientRingDescent constructs a ring map on A/I from an actual ring map
A->B killing I, including beta and the ring laws.

QuotientFibreBaseChange.Over[R,setR,I,propI,E] reuses QuotientFibre's
extended ideal IE, quotients and induced R/I scalar map. It constructs:
  algebra        the actual quotient E/IE as an R/I-algebra;
  projection     E -> restrict(algebra) as an R-algebra map;
  To[B]          inverse maps and equivalence
                   Hom_(R/I)(E/IE,B) ~= Hom_R(E,restrict B).

Presented[p,ps] exports the finite presentation obtained by mapping
each coefficient of p into R/I, on this actual quotient algebra. It
also exports unramified unique, by the checked arbitrary-base theorem.
This identifies the chosen quotient model by universal property rather
than assuming an isomorphism with an unspecified base-change model.

FiniteSpecialFibre applies UnramifiedFieldFiniteGeneral to this quotient
over LocalResidueField, then changes only the order of scalar products
to match QuotientFibre.ModuleFinite. A merely given original presentation
is eliminated directly into the truncated finite-module conclusion.

3. Checks

Fresh All.seg --opened: 13869 declarations, 0 failed, 5.89 s.
./segc sag/etale-field-fibre all: 320 modules, 0 failed.
Six owned files: 149 declarations; each rounds to 0.00 s and opens at
most 25 definitions. All 141 named declarations are covered by .opens;
each reports nothing else opened. Eight anonymous opens are omitted.

ResidueFieldRegression constructs the residue field of Z/4 with I={0,2},
defined by 2*a=0. SpecialFibreRegression runs the entire quotient-fibre
finiteness theorem over that nonreduced base for both the empty algebra
presentation and the point presentation X=2. A deliberate isolated
mutation asserting that the class of 1 is zero was rejected.

4. Boundaries

The selected-prime separable primitive-element theorem remains separate.
This does not yet lift its coefficient and generation identities into
SelectedFlatLocal. QuotientPowerClearing provides the needed explicit
powers for equations pulled back from a localised quotient; no injection
from B/IB to its localisation may be substituted for that argument.

All reused sources are unchanged relative links. Import ordering handles
existing local aliases Span, Spans and Expansion without editing shared
sources. No checker edits, new axioms, or commits.
