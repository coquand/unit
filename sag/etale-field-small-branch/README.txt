THE FINITE-COEFFICIENT-FIELD BRANCH OF SELECTED FACTOR EXISTENCE
============================================================

1. Checked endpoint
-------------------

SmallFieldBranch.Over[k,setk].At[S,input]
  .Coefficients[t,coefficients,K0].Given[reduced,lower,roots].result

has exactly the existing type

  SelectedFactorStatement.Over[k,setk].At[S].Result input.

The result merely provides an idempotent e outside the specified prime,
a generator gamma, a monic polynomial P over k, a derivative inverse on
eS, and polynomial representations of all the given basis vectors on eS.
The equations are exactly the existing Selected record, including the
factors e; no replacement or weakened output statement is used.

Inputs, stated honestly:
  k,setk       the base commutative set-ring;
  S            the k-algebra;
  input        SelectedFactorStatement.At[S].Input, carrying its discrete
               nonzero field law, actual finite basis and specified prime;
  K0           the ACTUAL finite Subfield record returned by
               FiniteCoefficientField for the finite coefficient family;
  reduced      square-zero elements of S are zero;
  lower        a coefficient list over K0 for each actual basis vector;
  roots        each basis vector satisfies that monic equation over K0.

The perfect-trace field carried by Input is not used in this branch.
The finite monic equations and reducedness remain explicit inputs here;
this directory does not claim to construct those inputs from perfect trace.

2. Construction
---------------

CoefficientSubalgebra is applied to the full family of basis vectors.
It constructs the finite K0-subalgebra B0, its actual finite enumeration,
and regularity inside B0. The specified prime restricts to B0. Its
Selected theorem merely supplies the appropriate idempotent.

Inside that truncation, SelectedFiniteImage.Chosen constructs the actual
finite field F, its injective enumeration and its map into S. The map
j:F->S is injective, additive and multiplicative, and sends 1 to e.
It is not asserted to be a unital map into S.

FiniteFieldPrimitive is applied over K0->F. It constructs gamma_F,
polynomial representations of every F-element, and the monic annihilator
T^Q-T with invertible dual-number slope. No primitive-element or
factorisation principle is an assumption of this branch.

The coefficient inclusion K0->k maps the returned lists. CornerHorner
proves the precise identities

  j(ev_F(p))    = e * ev_S(map(p)),
  j(slope_F(p)) = e * slope_S(map(p)),

at gamma=j(gamma_F). It then transports the root, derivative inverse,
and finite basis representations into the exact Selected statement.
The derivative inverse is j(-1), and the finite-field polynomial is
separable with that inverse on the selected corner.

The selected idempotent is used only inside the truncation that supplies
it. The final result is itself truncated, so no choice is made.

3. Generic reusable API
----------------------

CornerHorner.DualValues[K,A,setA,rho,x]
  first      first component of dual Horner equals ordinary Horner;
  slope-step the second component satisfies the differentiated Horner
             recurrence, with tangent 1.

CornerHorner.Over[R,K,F,S,setF,setS,coefficient,rhoF,rhoS,j,e,
                 zero,add,mul,one,constants]

Parameters are precisely:
  coefficient:R->K, rhoF:R->F, rhoS:K->S are unital ring maps;
  j:F->S preserves zero,+,*;
  j(1)=e;
  j(rhoF(a))=e*rhoS(coefficient(a)).

No unitality of j is assumed. No field law or idempotent law is needed
for these Horner identities; the displayed preservation laws suffice.
The record does not hide any flatness or quotient identification.

Its At[x] module exports value, slope, and represents. Its Monic[p]
module maps the monic list and exports value-law, slope-law, root,
and separable. These conclusions retain the factor e explicitly.

SmallFieldBranch contains one explicit monic-agrees lemma: the existing
SelectedFactorStatement and finite-field coefficient modules each define
append-one recursion, so their agreement is proved by list induction.

4. Regression
-------------

SmallBranchRegression runs the complete branch in F2 x F2 with the
first-projection prime. It uses the actual bounded coefficient-field
construction and the monic equations X^2-X for the two basis vectors.
It invokes the NEW finite-field primitive-element construction; the
older hand-written selected certificate is not used to obtain the result.
For each selected idempotent the output root and both basis-generation
identities are checked.

A separate concrete corner test uses j(a)=(a,0), e=(1,0), gamma=e and
P=T+1. It verifies:
  j(1)=e, and j is not unital into F2 x F2;
  P(e)=(0,1), hence P(e) is not zero in the ambient algebra;
  e*P(e)=0;
  the derivative inverse condition holds on eS.
This is a substantive regression for retaining the idempotent factor.

5. Validation
-------------

Fresh built-checker All.seg:
  11843 declarations, 0 failed, 4.75 s.
./segc sag/etale-field-small-branch all:
  286 modules, 0 failed, 4.23 s.

The three owned modules contain 121 declarations:
  CornerHorner          52
  SmallFieldBranch      41
  SmallBranchRegression 28

--opened: at most 29 distinct definitions opened and at most 0.01 s for
an owned declaration in the fresh run.
--opens etale-field-small-branch.opens: all 121 owned declarations are
covered and every one reports "nothing else opened".

Two mutations were checked in an isolated /tmp copy; working files were
never mutated:
  * omit e from the corner value identity;
  * replace tangent 1 by tangent 0 in dual Horner evaluation.
Both were rejected by the checker. The latter also fails the assembled
separability theorem and its concrete regression.

All reused modules are relative links. No new axioms, checker edits,
shared-file edits or commits. There was one compatibility rename in our
previous owned finite-primitive development: GcdStripping's local module
Loop became StripLoop to avoid the existing global Loop name. Its public
API is unchanged. Its fresh recheck gives 2289 declarations, 0 failed;
all 812 entries of its updated opens spec are clean.

6. Remaining outside this branch
--------------------------------

The remaining global field proof must produce the finite family of monic
annihilators, collect/lift their coefficients into K0 in the small branch
of the bounded coefficient-field alternative, and supply reducedness.
The large-field branch is separate. This theorem completes the actual
selected-factor construction once those displayed inputs are supplied.

The checking server is stopped.
