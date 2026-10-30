Actual chart error-witness realization
======================================

Owned source: ChartErrorWitness4.seg (38 declarations).
All other sources are unchanged relative links. No new axioms, no choice,
no coherence/Noetherianity hypotheses, no checker or shared-source edits.

Exact API
---------
ChartErrorWitness4.Over[A,setA,E,t,b,s,p,e,hp,k]
  A any set-ring; E any four-coordinate chart subset;
  b a finite ideal generator list; p a finite homogeneous polynomial list,
  with the supplied natural degrees e and proofs hp; k any integer.

.D and .R are ChartDegreePart4 and its native ChartLaurentRing4 instance.
.Part = D.Part[k].Into[Sq].
.CJ = ReesChart4.Over[A,setA,t,b,s,p,e,hp].JC[Sq,constant E,k].
.W = SectionsErrorWitness over R.ring, generators iota(b_j), and
  J_q = inclusion(phi(p_q)).

.Realize[depth,x,wit], where wit : W.Witness depth x, exposes
  w         : CJ.E.El
  ideal     : CJ.FC.Wit depth w
  remainder : CJ.JW(CJ.ML.msub(Part.element x) w)
  result    : (v:CJ.E.El) *
                (CJ.FC.Wit depth v * CJ.JW(Part.element x - v)).

The construction is explicit: w is the degree-k part of the source ideal
witness. IdealPowerWitnessTransport maps every node of its witness tree.
Each original J multiplier y_q maps to Part_(k-e_q)(y_q). The proved
ChartPartMultiplication4 identity factors p_q out of this projection;
finite-sum preservation and subtraction preservation produce the exact
original defining-list J-witness. No Laurent generation is assumed.

Scope includes empty ranks, depth zero, negative twists and all chart
subsets. This is a local assembly helper, not a theorem constructing
finite-fibre sections or full ZMT. The section agent supplies the explicit
source Witness; this helper realizes it in actual singleton chart modules.

Dependencies
------------
Native Laurent child: ChartLaurentRing4, ChartCoefficientSupport4,
ChartDegreePart4, ChartPartMultiplication4 (and LaurentPowerRing4).
Root completion: SectionsErrorWitness, IdealPowerWitnessTransport and their
existing arithmetic dependencies. Existing ReesChart4 supplies target JW.
No restriction/inverse-coordinate or Section construction is imported by
this source. All.seg additionally imports the root completion baseline.

Auditing
--------
The .opens file records all 38 own declarations' measured opened names;
it is a transparent unfolding inventory, not an independently minimal
allowlist. Exact validation results are recorded in VALIDATION.txt.
