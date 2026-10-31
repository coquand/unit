Gaussian coordinates near one specified prime
=============================================

SelectedGaussianConstruction.Over[A,q,regular].theorem n m v
  : || SelectedGaussian.Over[A,q,regular].NormalForm[n,m,v] ||

A is any commutative ring, q a proposition-valued decidable proper prime,
and regular gives merely b with a=a*a*b for every a. The finite relation
matrix v has m columns in A^n. No field hypothesis on A is made.

The constructed normal form contains:
  e, with e*e=e and e outside q;
  an actual rank r;
  A-linear maps P:A^n->A^r, S:A^r->A^n, D:A^n->A^m;
  e*(P(Sx)-x)=0;
  e*P(v_j)=0;
  e*(v(Dx)-(x-S(Px)))=0.

All three displayed equations are coordinatewise. Restriction to eA
makes them exact Gaussian quotient coordinates; the actual module and
algebra basis adapters are in etale-field-selected-basis.

Construction
------------
RegularPrimeQuotient constructs the actual discrete nonzero field A/q.
The inverse of a nonzero class comes from a regular witness for a.
Quotient induction and truncation eliminate only into propositions;
there is no globally chosen representative function.

GaussianQuotient, reused unchanged, runs on the relation matrix over A/q.
FiniteMatrixCoordinates expresses its linear maps by standard columns.
Finite choice lifts only P, S, and the difference coefficients on the
standard basis. The three finite lists of equation errors lie in q.

SelectedAnnihilator kills any such finite family by an idempotent outside
q: for a=a*a*b in q, 1-a*b is an idempotent outside q and kills a.
Multiply these finitely many idempotents. Linearity then extends the
matrix-column identities to all vectors. This proves the normal form
without constructing a decomposition of A into all its components.

Files and validation
--------------------
Six owned .seg files, 288 declarations. Fresh All.seg --opened:
7800 declarations, 0 failed, 2.97 s. segc all: 179 modules, 0 failed.
Every owned declaration takes at most 0.01 s and opens at most 30
definitions. All 277 named declarations have clean .opens entries;
11 anonymous opens are omitted.

SelectedGaussianRegression uses F2 x F2 with the prime of the first
projection. It constructs the annihilator (1,0) of the nonzero element
(0,1), applies the full theorem to a relation supported differently on
the two factors, and checks the empty module and relation-free cases.
An isolated mutation replacing the lifted projection matrix by zero
is rejected by the checker. Original files are unchanged by that test.

All reused files are unchanged relative links. No new axioms, checker
changes, shared edits, or commits. This is the selected finite-matrix
step; it does not by itself prove the primitive-element theorem.
