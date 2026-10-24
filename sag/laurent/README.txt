Picard group of P^1, worker B: polynomial and Laurent algebra
=============================================================

Check from the repository root:   ./segc sag/laurent all
Independent check:     (cd sag/laurent && "$(cabal list-bin exe:seg)" All.seg)

Deliverable: LaurentResults.Over[R,setR,sag].results : PicardInterface
.AlgebraResults (picard/PicardInterface.seg, owned by worker A), built
from SAGAxioms.Assumptions alone (Loc and uniform SQC; Z-choice unused).
No postulates. Dependencies are read-only relative symlinks; the base is
the opens/ library up to Units23, plus torsor/Torsor and A's
PicardUnits and PicardInterface.

Units are pairs (x, unit x); a "polynomial unit" is a function R -> Units
and a "Laurent unit" a function Units -> Units, as in the interface.
Coefficient lists are polynomial/Poly and polynomial/Mul.

LocalizationKernel.seg   (no axioms)
  If a maps to 0 in A[1/f], then merely f^k a = 0 (kernel certificate of
  A[Y]/(fY-1) plus the linear-certificate calculation).
UnitVanishing.seg        (SQC)
  A coefficient list whose values at all units vanish is 0: R[X][1/X] is
  finitely presented, its points are the units, then the kernel lemma.
ChartIntersection.seg    (SQC)  -> interface field `intersection`
  Every f : R -> R is merely a polynomial; f(x) = g(1/x) on units makes
  f and g constant (induction on g's coefficients, base case above).
UnitPowers.seg           (no axioms)
  Group calculations in the units; comparison of natural numbers.
DegreeUnique.seg         (SQC, 1 /= 0)  -> field `degree-unique`
  x^N a(x) = x^M b(1/x) forces N = M: otherwise ChartIntersection makes
  the unit b(0) (or, with the charts exchanged and inverses, a(0)) zero.
LaurentRep.seg           (SQC)
  Every phi : Units -> R is merely y^N p(x), y = 1/x (fractions in the
  localization).
Split.seg                (SQC)
  Every phi : Units -> R is merely g(x) + h(1/x).
NilFactor.seg            (SQC, 1 /= 0)
  1 + n mu with n nilpotent factors as a(x) b(1/x): split mu, peel off
  (1 + e g)(1 + e h), the error moves from e = n^(r+1) to n^(r+2); then
  a finite list of such terms is absorbed one after the other.
TopCoefficient.seg       (no axioms)
  Copy of bounded/Mul.seg TopR: degree >= 1 with a unit top coefficient
  is not invertible.
Pivot.seg                (SQC, Loc)   Lemma 4.1 for R
  If P Q = X^K and P(1) is a unit: merely P_i is a unit and every other
  P_j is not not 0. P(1) = sum of coefficients gives i by Loc; the second
  part is negative, so the coefficients are decided (0 or a unit by
  2.2.3(b)) and lowest/highest coefficients plus TopCoefficient leave a
  single nonzero coefficient.
Factorisation.seg        (SQC, Loc)  -> field `factorisation`
  Lemma 4.4, existence: t = c x^(i-N) (1 + nilpotent terms), then
  NilFactor; nilpotence of the terms from 2.2.3(c).
LaurentResults.seg
  The record of the three fields.
