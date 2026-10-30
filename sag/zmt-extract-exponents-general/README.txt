zmt-extract-exponents-general: prescribed denominator and exponent helpers
========================================================================

These three new sources prove the finite-coordinate algebra needed for
prescribed-denominator polynomialization and affine extraction. No prior
source/checker/git file is modified. Imports are relative links. There are
no additional axioms, choice principles, coefficient decisions or rank/
nonnegativity hypotheses hidden in the chart clearing statement.

PrescribedChartClearing.Over[A].Clearing[n,E,S,u,off,dom]
 .Function[f,supp,van].polynomial
has EXACT type
 (v:GenericLaurent.Exp n)(i:Fin n) -> Laurent4.Neg(v i) ->
 Id A.R (f(ChartDenominators.down n v u)) A.z.
Here off says flag(E,i)=absent implies u_i=0; dom says for every exponent
w in S and every inverted coordinate i, negPart(w_i)<=u_i. supp says f=0
outside S; van says f=0 on chart-forbidden exponents. The proof uses off
on an outside coordinate and dom+finite support on an inverted one. It
works for any bitset, including the empty set, and any finite support
list, including lists containing exponents at which f is zero. This is
precisely the polynomial premise of PrescribedPolynomialization.Clear.

CoordinatePowerExponents.powAxis n i k has exponent k at coordinate i and
zero elsewhere, defined through the singleton chart flags. degree proves
its natural total degree k. axis-one identifies k=1 with the native chart
coordinate exponent. Monomials[E].value proves its actual affine monomial
value is y_i^k. singleton-only, empty-flag and empty-power provide the
structural finite-index lemmas used in the bound proof.

ExtractionBounds.Over[m,S], n=suc m, Z=inr tt:
 BZ = CD.amount n Z S; kZ = suc BZ;
 Bi i = CD.amount n (inl i) S; ki i = suc(Bi i);
 LZ = N.join m (N.zeroE m) kZ;
 Li i = N.join m (powAxis m i (ki i)) zero;
 LE i = addN LZ (Li i);
 LZ0 = N.join m (N.zeroE m) BZ.

ZChart.off/dom, IChart[i].off/dom and Edge[i].off/dom satisfy the EXACT
prescribed-clearing interface for respectively singleton(Z),
singleton(inl i) and pairSet(inr i) = {Z,inl i}. Thus these denominators
clear all the actual extraction point/overlap coefficients with one
common finite support S. Each bound has been increased by one already.

The exponent equalities are:
 shift-oneZ v: (v-LZ)+NativeAxis(Z) = v-LZ0;
 shift-both v i: (v-Li)-LZ = v-LE;
 shift-both-commuted v i: (v-LZ)-Li = v-LE.
degree-Z and degree-i give the exact degrees kZ and ki.
Monomials[E,y].value-Z, .value-i, .value-edge give the dehomogenized
monomial values 1, y_i^ki and y_i^ki, respectively. Orientation is newest
vertex first, and no fixed-dimension sign table or Fin4 exponent is used.
Empty affine dimension m=0 is included: only the Z singleton remains and
the I/Edge declarations quantify over the empty Fin0 type. Nothing here
asserts a projective interpretation of the augmented n=0 complex.

These are exponent/clearing lemmas, not the final extraction theorem.
The source functions need not be homogeneous; PrescribedPolynomialization
and its separate degree proof handle that part in the extraction track.
