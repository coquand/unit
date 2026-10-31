Equations in a localised quotient, with explicit powers
=====================================================

QuotientPowerClearing.Over[B,I,propI,s] constructs Q=B/I and
T=Q[1/[s]], using the existing effective quotient and fraction rings.
eta:B->T is their composite ring map. No set, reducedness, field,
flatness or injectivity hypothesis on B->T is supplied.

Witness b = (N:Nat) * I(s^N*b).

  clear b eq         eta(b)=0 -> merely Witness b;
  vanish b w         Witness b -> eta(b)=0;
  clear-equality     eta(b)=eta(c) -> merely Witness(b-c);
  clear-family       finite many equations -> one truncated finite family
                     of explicit exponent/ideal witnesses.

The proof uses the effective power-localisation kernel, then the
effective quotient kernel. In the reverse direction, eta(s) is a unit,
so its power can be cancelled. No equation is pulled back by an assumed
inclusion Q->T.

QuasiInverse[N,v,relation] takes I(s^N*(1-s*v)). It proves eta(v) is
the inverse of eta(s), then:

  onto x : merely (b:B) * eta(b)=x.

For a fraction with numerator represented by b and denominator s^n,
the representative is b*v^n. Quotient and fraction representatives are
chosen only inside truncation. Zero targets and N=0 are allowed.

Validation

Fresh All.seg --opened: 1666 declarations, 0 failed, 0.36 s.
Two owned files: 74 declarations, each rounds to 0.00 s and opens at most
22 definitions. The .opens audit covers all 71 named declarations.

Regression: B=Z/4, I=0, s=2. The image of 1 vanishes and yet 1!=0 in B;
the explicit witness has exponent 2. The localisation is still merely
covered by B using v=0. The s=1, N=0 case also checks. An isolated
mutation replacing the required exponent 2 by 0 was rejected.

These generic lemmas do not yet identify a chosen special fibre with
the mapped-presentation base change, or lift every selected-factor datum.
Those remain integration obligations. All dependencies are unchanged
relative links; no new axiom, shared-source edit or checker change.
