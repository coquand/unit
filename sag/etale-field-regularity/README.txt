Field regularity from formal unramifiedness
==========================================

Status: checked. No new axioms, checker edits or shared-file edits.
Reused files are relative links. Nothing is committed.

1. Main theorem

UnramifiedFieldRegular.Over[k,setk,dec].At[S,fp,unique]

Inputs: a commutative set-ring k with a zero-or-unit operation dec; a
commutative set-valued k-algebra S; a merely given finite presentation
fp; and FormallyEtale.Unique S (uniqueness of square-zero lifting).

  regular: every a in S merely has b with a=(a*a)*b.
  reduced: every nilpotent a equals zero, including exponent zero.
  zero-dimensional: every a merely has N,b with a^N(1-a*b)=0.

The theorem does not take flatness transfer, a diagonal, a finite basis,
or ZMT as a parameter. FlatDiagonalTransfer constructs the diagonal and
base-change algebra. FieldFlat proves every target k-algebra is k-flat
from finite relations. Applying these to the effective quotient S/(a)
and then FlatQuotient yields the regularity witness. No global choice
of representatives or bases is used. Nontriviality of k is not needed
for regularity; thus the zero-ring case is also included.

2. Completed one-generator consequence

UnramifiedFieldFinite.Over[k,setk,dec,nonzero].One[S,x,gen,fp,unique].finite
gives a fixed finite spanning family over k, merely. Here nonzero is
1 != 0 and gen is expression generation by x. The Presented adapter
takes an actual finite presentation with one variable and derives gen
and fp from it. MonogenicExpressions and MonogenicFinite construct a
nonzero relation X^N(1-X*P), normalise it to monic, and divide by it.
The arbitrary-arity result now also checks:

UnramifiedFieldFiniteGeneral.Over[k,setk,dec,nontrivial].At[S,fp,unique]
  finite: FiniteSpan.Over[k,S.ring,S.iota].Finite
  integral: IntegralDescent.Map[k,S.ring,S.iota].Extension

This takes only the field laws, finite presentation and formal
unramifiedness. Generation is derived from the presentation. The
constructed ZeroDimensionalFinite theorem in etale-field-generated
works for any number of generators; its Nagata reduction and integral
descent are proved. No basis, transfer principle, or ZMT is assumed.

3. Files owned here

FieldFlat: explicit finite relation explanations, all-zero or unit pivot.
PrincipalRegularity: flat principal quotient implies a=a^2*b. Its Field
  adapter still explicitly takes transfer; the main theorem above uses
  the fully constructed transfer and does not have that parameter.
RegularReduced: regularity implies reducedness.
UnramifiedFieldRegular: the unconditional first milestone.
UnramifiedFieldFinite: its completed one-generator finiteness consequence.
UnramifiedFieldFiniteGeneral: the arbitrary-arity finiteness theorem.
FieldRegression, FieldRegularRegression, FieldFiniteRegression: regressions.

4. Regressions and validation

F2 with an infinite polynomial target, F2[t]/(t^2), the empty relation,
the all-zero row and the actual computed pivot columns; principal
quotients of F2; and a constructed standard algebra for X^2-X over F2,
on which regularity, reducedness and zero-dimensionality all apply.
Evaluation at one proves its distinguished generator is nonzero.
The full finiteness theorem is applied to this quadratic's actual
standard-algebra presentation and to the empty presentation of F2.
The generator induction is also instantiated with three redundant
generators, without any finite-presentation hypothesis.

Fresh All.seg --opened: 9985 declarations, 0 failed, 3.69 s.
Nine owned modules: 283 declarations; every one takes at most 0.01 s
and opens at most 29 distinct definitions. The opening specification
covers all 269 named declarations (14 anonymous opens are omitted).

Two isolated mutation tests were rejected: removing the minus sign in
the pivot columns, and changing the regularity conclusion to a=a*b.
Original files were not modified during these tests.

5. What remains

Basis construction from finite algebra presentation, the selected-prime
primitive element, and the residue-field bridge are separate obligations.
The trace theorem in etale-field-trace has an
explicit finite-basis input; regularity alone does not supply that input.

The opening audits include quotient carrier and operation aliases where
the effective principal quotient is instantiated, and concrete F2 and
standard-algebra computations in the regression files. They are a
comparison-cost regression specification, not additional kernel trust.

Check with ./segc sag/etale-field-regularity all from unit/.
