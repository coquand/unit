Derivations on a selected idempotent factor
=========================================

IdempotentDerivation.Over[k,setk,S,e,he].Given[d]
restricts an actual relative k-derivation d:S->eS along the canonical
projection to a self-valued derivation of eS. Its interfaces are:
  idempotent-zero: D(e)=0;
  linear, product: the restricted derivation and its Leibniz law;
  on-project: D(e*a)=D(a);
  Trace[n,basis].theorem nondegenerate a: D(a)=0.

The last theorem assumes only trace nondegeneracy on eS, with its actual
finite k-basis. A basis or nondegenerate trace on all of S is unnecessary.
The proof of D(e)=0 cancels D(e) from D(e)=D(e)+D(e); it never divides by 2.

This adapter lets a derivative annihilator in e(k[T]/f) give a derivation
of that selected factor. TraceDerivations then kills the annihilator,
and regularity makes the projected derivative a unit. The assembled
selected separable-annihilator theorem is in etale-field-selected-separable.

Validation: fresh All.seg --opened 9267 declarations, 0 failed, 4.05 s;
segc all 218 modules, 0 failed. The two owned files have 48 declarations;
each rounds to 0.00 s and opens at most 33 definitions. All 44 named
declarations have clean .opens entries; four anonymous opens are omitted.

The regression uses F2[epsilon]/epsilon^2 and its nonzero derivation
D(a+b*epsilon)=b. Restriction to the unit factor still sends epsilon to
1. This tests characteristic 2 and the necessity of trace nondegeneracy
for the final vanishing theorem. An isolated mutation replacing this
value 1 by 0 is rejected; original files are untouched by the mutation.

All reused sources are unchanged relative links. No new axioms, shared
edits, checker edits, or commits. The checker server is stopped.
