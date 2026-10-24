Projective space P^n (projective.pdf, Section 1 and Section 7)
==============================================================

Main results, from the SAG axioms Loc, SQC and Z-choice:
  Theorem73.theorem-7-3   line bundles on P^n are Line x Z (n >= 2;
                          Theorem73One: n = 1);
  AutPn.corollary-5-6     Aut(P^n) = PGL_{n+1}(R) (n >= 1).

Check from this directory:
  "$(cabal list-bin exe:seg)" All.seg
0 failures, 4.4 s (the whole Picard library is imported:
Theorem 7.3 uses Proposition 4.6).
Library files are links into ../picard; TruncatedMap and SurjectiveEmbedding link into ../projective.

For any commutative ring R with a set carrier, and n : Nat:

ProjectiveQuotient.Over[R,setR,n].Pn               definition (ii)
  Vectors of R^{n+1} with some coordinate invertible, modulo y = u x for a
  unit u.  The relation is a proposition, and is equivalent to
  proportionality x_i y_j = x_j y_i (related-proportional, FromProportional).

ProjectiveLines.Over[R,setR,n].Pn                  definition (i)
  (l : Line) * (l^{n+1} \ {0}).  Line is the type of R^*-torsors of
  PicardLines; l^{n+1} is the maps v : T -> R^{n+1} with v (g t) = g^-1 v t.
  set: this type is a set (the action is free).

ProjectiveSpace.Over[R,setR,n].equivalence : Equiv Ln.Pn Q2.Pn
  (l,v) |-> [v t] for any point t of l;  [x] |-> (trivial line, s |-> (s-t0)^-1 x).

ProjectiveSAG.Over[R,setR,n,sqc,loc].points
  With Loc and SQC, "some coordinate invertible" is x /= 0 (SAG 2.2.3(b)),
  so the points of (ii) are exactly R^{n+1} \ {0}.

Section 7 of projective.pdf, with SAG's SQC and Loc (and Z-choice for 7.2, 7.3):

PuncturedSpace.Over[R,setR,sqc,m].lemma-1-6            Lemma 1.6
  For k = m+2 >= 2, restriction (R^k -> R) -> (R^k \ {0} -> R) is an
  equivalence.  From an abstract Hartogs lemma (Hartogs, VectorHartogs):
  on Spec A with regular s_0, s_1, .. such that s_1^b g = s_0^a h implies
  s_0^a | g, functions on D(s_0) u D(s_1) u .. are elements of A.
ProjectiveFunctions.Over[R,setR,sqc].Space[m].constant  Proposition 1.7
  Every map P^n -> R is constant (n >= 1).
Lemma71.Over[R,setR,m,sqc,loc].lemma-iv / -iii / -ii / -i   Lemma 7.1
  For n = m+2 and p /= q, maps P^n \ {p,q} -> R, P^n \ {p} -> R and the
  same to Z are constant.  p, q are moved to [e_Y], [e_Z] by a linear
  automorphism (TwoPoints, ProjectiveLinear); there the complement lifts
  to D(X) u D(YZ) u D(other coordinates), a Hartogs family (NormalPair).
  The paper's proof uses charts and gluing; this route needs neither.
LineMaps   the line P^1 -> P^n through [x] /= [y]: [a:1] |-> [a x + y],
  [1:b] |-> [x + b y], on the two-chart P^1 of Proposition 4.6.
Twist.Over[R,setR,n,sqc,loc].O d : P^n -> Line                 O(d)
  The fibre at p: unit-valued functions v on representatives of p with
  v(u x) = u^d v(x); so O(1) is dual to the tautological line.  Restricted
  to a line it is the O(d) of Proposition 4.6 (Restrict.restrict).
Theorem73.Over[R,setR,m,sag].Lemma72[x,y,ne].lemma-7-2          Lemma 7.2
  Gr(1,M) is parametrised by P^1 through the basis x, y of M; the map
  (a,d) |-> (L |-> a (x) O(d)(L)) is then Proposition 4.6's equivalence.
Theorem73.Over[R,setR,m,sag].theorem-7-3                        Theorem 7.3
  For n >= 2, Line x Z -> (P^n -> Line), (a,d) |-> (x |-> a (x) O(d)(x)),
  is an equivalence.  The inverse is L |-> (L([e_Z]), degree of L on the
  line through [e_Y], [e_Z]).  The main step (LineAgreement): two bundles
  that agree on one line are merely equal.  Agreement on the lines through
  p is decidable (compare degrees), so Lemma 7.1 (i) spreads it to all
  lines through p; an identification at p extends uniquely along each
  line, two such (at p and q) differ by a constant unit (Lemma 7.1 (iv)),
  and after correction they glue.  The paper's tensor algebra
  (L (x) O(-d)) is not needed.
Section 7 files: 1897 lines; the slowest, NormalPair, checks in 0.25 s.

Aut(P^n), Corollary 5.6 of projective.pdf, for every n >= 1:
AutPn.Over[R,setR,sag].Line.corollary-5-6            n = 1
AutPn.Over[R,setR,sag].Higher[m].corollary-5-6       n = m+2
  both instances of
AutPGL.Over[R,setR,n0,sag,cls].corollary-5-6 : isEquiv PGL Aut aut-of
  for n = n0+1, where cls is the classification of line bundles on P^n
  (Classification.Theorem: (a,d) |-> a (x) O(d) is an equivalence
  Line x Z -> (P^n -> Line)); this is the only use of Theorem 7.3.
  For n = 1 it is Theorem73One: P1Compare shows that the two-chart P^1
  of Proposition 4.6 and the quotient P^1 are equivalent (the line through
  e_X, e_Y is injective and surjective), and along it a (x) O(d) restricts
  to Proposition 4.6's classification (as in Lemma 7.2).
  GL: linear automorphisms of R^{n+1}; PGL: GL modulo unit scalars; Aut:
  maps P^n -> P^n with an inverse; aut-of: the action, which respects
  composition (act-compose).  The proof avoids the paper's Corollary 5.5:
  Lift        a map P^n -> P^t lifts to F with F(u x) = u^d F(x), using
              Theorem 7.3 and the frames of O(d) (no tensor powers).
  Weights     by Lemma 1.6: negative weight forces F = 0; a function that
              is a unit off 0 is a unit at 0, so it has no weight >= 1.
  AutLinear   for phi with inverse psi, G(F x) = lambda(x) x forces both
              weights to be 1; lambda is constant (Proposition 1.7).
  WeightOne   a function of weight 1 is additive (by the chart
              intersection lemma), so F is linear.
  AutPGL      injectivity, and the equivalence.
These files: 619 lines; each checks in at most 0.25 s.  The n = 1 files
(P1Compare, Classification, Theorem73One, AutPn): 200 lines, each < 0.1 s.

Assumptions: univalence and replacement (All.seg); the SAG axioms SQC, Loc
and Z-choice only as module parameters, where named above.  No postulates.
Nothing is committed.
