sag/zmt-lifting: finite relation certificates (Stage 1) and the
four-coordinate cubic test J = (X_0^3, X_1^3) (Stage 2)
=====================================================================

Task: doc/zmt-lifting-handoff.txt, doc/zmt-lifting-command.txt.
Companion proof: doc/zmt-formal-cohomology.tex ("A further shortcut: do
not generate the finite kernel", "The minimal relation-certificate
interface", the four-coordinate remark).

STATUS (30 October 2026).  Both stages are formalised and checked.
  Stage 1: the abstract relation-certificate lemma with partners given
           only under truncation, with no choice of a sequence of partners.
  Stage 2: the cubic certificate relation is CONSTRUCTED (Laurent modules,
           Cech differential, contractions, top coordinates, raising,
           closure, zero-reflection) over any commutative set-ring D, and
           Stage 1 is instantiated for it when D is CFN (and for D = Z).
  This is a test of the finite-coordinate mechanism.  It is NOT full ZMT,
  a general finite-fibre lifting theorem, the Rees comparison, or
  projective finiteness in arbitrary dimension (see OUT OF SCOPE).

Check:   ./segc sag/zmt-lifting all            (from unit/)
Fresh:   cd sag/zmt-lifting && $(cabal list-bin exe:seg) All.seg
Audit:   ... All.seg --opened ;  ... All.seg --opens zmt-lifting.opens


1. FOUNDATIONS AND PARAMETERS
-----------------------------
All.seg is the segment Theory with the standard parameters of sag/:
  univ        : [l] Axioms[l].Univalence
  images      : [l][k] Replacement[l,k].Images
  surjections : their surjectivity
FunExt (fe) and propositional univalence (propUA) are derived exactly as
in sag/artin-rees.  Propositional truncation is Truncation.Trunc (from
replacement).  No new axioms: no SAG/SQC, choice, excluded middle,
propositional resizing or noetherian axiom; the checker is unchanged.

Algebraic parameters of the theorems (nothing else):
  D : CRing                      (Stage 1 and Stage 2)
  setD : isSet D.R               (Stage 2: the chart conditions are
                                  propositions; "commutative set-ring")
  cfn : CFN.CFN K0 D, K0 : U l   (Stage 1 and the final instance only)
Universe levels: everything lives at the single level l of the files
(D.R, the module Z, B, Gam, the prefixes and the goal are in U l; the
principle of free lists quantifies over U l-valued predicates).  No
resizing is used.

Files (new):  RelationCertificate, CertifiedDependence, LinearCertificate
              (Stage 1); Laurent4, Cech4, Cech4Contraction, TopList4,
              TopCoordinates4, CubicCertificate, CubicDependence,
              CubicExample (Stage 2); All.seg; zmt-lifting.opens.
Links (unchanged libraries, relative symlinks to their real location):
  core: Base Prelude Paths Axioms FunExtUA; the Ring/polynomial/algebra
  prerequisites of sag/artin-rees; IdealPowers (modules, Lin), Comb,
  ModSpan, Coherent, Spans, FreeCoherent, FreeDisc, FreeNoeth, LinIso,
  CodedNoeth, CFN (CFN rings, (D), (FL) for D^v); ZInt (the integers),
  Laurent3, Cech3, CechContraction, CechMonomials, LaurentList, CechModules
  (only CechModules.SubMod and .comp, and Laurent3's dependencies, are
  used); Integers, ZRing, ZArith, ZCFN (Z is CFN, for the Z instances).


2. STAGE 1: THE RELATION-CERTIFICATE LEMMA
------------------------------------------
Data (RelationCertificate.Rel D Zm Vm), for D-modules Z = Zm, V = Vm:
  B   : Z -> U l,   Gam : Z -> V -> U l,
  gam-zero : Gam(0,0),
  gam-add  : Gam(z,p) -> Gam(z',p') -> Gam(z+z', p+p'),
  gam-sm   : Gam(z,p) -> Gam(c z, c p),
  reflect  : Gam(z,0) -> B(z)                       (zero-reflection).
Negation/subtraction is derived (Over.gam-sub, via the scalar -1).  B
needs no submodule structure; neither B nor Gam needs to be
proposition-valued or decidable (the proof uses none of this), so the
theorem holds in particular for propositions.  Z need not be finite,
discrete or noetherian.

Sums: for b : Nat -> Z and qs = [q_(N-1),..,q_0] (head last added),
  sumL [] = 0,  sumL (q :: qs) = q b(len qs) + sumL qs   (Over.Seq.sumL),
so sumL qs = sum_{i<N} q_i b_i with N = len qs, and
  Cert = (qs : List D) * B(b(len qs) - sumL qs)           (RC), N = len qs.

THEOREM (CertifiedDependence.Over[K0,D,cfn,Zm,v,R,b,partner].certificate).
  D CFN, Z a D-module, v : Nat, V = D^v (Comb.Free D v), R : Rel D Z V,
  b : Nat -> Z, and
    partner : (n : Nat) -> || (p : V) * Gam(b_n, p) ||.
  Then  || Cert ||, i.e. merely N, q_0..q_(N-1) with
    B(b_N - sum_{i<N} q_i b_i).
  N = 0 (empty sum) and v = 0 are covered by the generic proof.

Proof and correspondence.
  * RelationCertificate.Over.Seq.Prefix n: a list of n CHOSEN partners
    with their certificates (p_i, g_i : Gam(b_i,p_i)), i < n; partners
    lists them.  Only finite prefixes ever exist.
  * reduce (zero vector => (RC) from a dependence): for a prefix c of
    length n, Gam(z,y) and y in the span of partners c, there is qs of
    length n with B(z - sumL qs).  Induction on n: y = 0 gives B(z) by
    reflect; at n+1, y - k p_n in the span of the rest, Gam(z - k b_n,
    y - k p_n) by closure (gam-sub), and the induction hypothesis (peel).
    dependent: the case z = b_n, y = p_n.
  * CertifiedDependence: Chi s = for every n and prefix c of length n with
    span s in span(partners c), merely a certificate (a proposition).
    Step (Step, step): eliminate ONE truncated partner of b_n into this
    proposition (TC.rec (partner n)); decide p in span s by (D) for D^v
    (FreeDisc.disc-vec, Spans.dec-list).  If yes: dependent.  If no:
    extend the prefix by (p,g) and use Chi(p :: s) at n+1.  The principle
    of free lists for D^v (FreeNoeth.fl-vec, from CFN) gives Chi [] at n=0.
  No function Nat -> V, and no countable choice, is used: the only
  eliminations of truncations are of the single partner at the current
  index, into a proposition.  Coefficients are retained (Cert carries qs).

Instance (LinearCertificate): for L : Lin D^v -> Z,
  Gam(z,p) := z = L p,  B(z) := z = 0;  rel, Dep.certificate:
  if every b_n is merely in the image of L then merely
  b_N - sum_{i<N} q_i b_i = 0.  at-zero: the instance v = 0.
Generic helper: RelationCertificate.LinL (f-zero, f-neg, f-sub of any
linear map), used in both stages.


3. STAGE 2: THE FOUR-CHART CUBIC CERTIFICATE (any commutative set-ring D)
-------------------------------------------------------------------------
3.1 Laurent elements (Laurent4).  Exponents E4 = Z^4 (ex a b c d),
  deg, Neg; X_0^3 is the shift sh0 (f(m - 3e_0)), X_1^3 is sh1, X_0^-3 is
  up0; sh-comm (P Q = Q P), up0-sh0, sh0-up0, deg-sh0/-sh1/-up0.
  A family c : I -> Z^4 -> D is a Laurent element in each component when
  it is finitely supported:
    Supp c = || (S : List E4) * (forall i m, m not in S -> c_i(m) = 0) ||
  (finite-support witness retained; c_i = sum_{m in S} c_i(m) X^m).
  Chart conditions: Van c = forall i m, Bad i m -> c_i(m) = 0.
  Chart I Bad: the D-module of such families (CechModules.SubMod), with
  accessors val/supp/van/mk and eq (equality by coefficients).
  Restrict: a raw linear map preserving Vanish (via a list map) and Van
  restricts to the chart modules.  Sub4/Out: Out E m = some coordinate
  outside E has a negative exponent; out-face, out-sh0/1, out-swap0..3,
  out-full.  dec-e4: equality of exponents is decidable (sign/value
  decisions on Z only).

3.2 The complex (Cech4).  Components p0..p3, e01..e23, t012..t123, s0123
  (4, 6, 4, 1); Bad k E m = deg m /= k or Out E m; Deg[k].C0..C3 = C^q(k).
  Fixed alternating convention:
    (d c)_ij   = c_j - c_i,
    (d c)_ijk  = (c_jk - c_ik) + c_ij,
    (d c)_0123 = ((c_123 - c_023) + c_013) - c_012.
  d0/d1/d2 raw, linear (d0-add .. d2-sm, rd0..rd2), preserve chart
  conditions (VanD.d*-van) and finite support (VanD.d*-vanish);
  D0 k, D1 k, D2 k : linear maps of chart modules.  DD0, DD1: d d = 0.
  Shift[I,set,k].P, .Q : C(k) -> C(k+3) (any component type);
  Pinv[k].lin = X_0^-3 : C^3(k) -> C^3(k-3).  Comm[k].d0-P .. d2-Q: d
  commutes with P, Q; PQ[I,set,k].comm: Q P = P Q.

3.3 Contractions (Cech4Contraction), for every k.
  Signs/sel: selection of the first coordinate with exponent >= 0 (sign
  decisions on Z, no decision in D).  cone1/2/3: the cone at a fixed
  vertex j, (cone_j c)_E = (-1)^p c_(E+j) (j not in E), 0 (j in E).
  htpy1, htpy2, top3: d cone_j + cone_j d = id on C^1, C^2 and
  d cone_j = id on C^3, at every exponent: 44 identities in D of 16
  shapes H1..H16 (each shape proved by hand; the case tables were
  generated from a symbolic computation of the signs and are checked by
  Unit; a deliberately flipped sign is rejected).
  h1, h2, h3 (selected contraction) and pi; htpy1-sel, htpy2-sel,
  top3-sel: d h c + h d c = c (q = 1, 2, c with chart conditions) and
  d h w + pi w = w; van-h*, vanish-h*, van-pi, vanish-pi.
  Contr[k] (the acceptance targets):
    (a) piE : C^3(k) -> C^3(k), the all-negative monomials;
    (b) sigma : C^3(k) -> C^2(k), sigma-eq : d (sigma w) + pi w = w;
    (c) con2, con2-eq : closed c in C^2(k) gives a with d a = c
        (used at k = -4);
    (d) con1, con1-eq : closed c in C^1(k) gives h with d h = c
        (used at k = -1);
        pi-d : pi (d u) = 0 for u in C^2(k).
  Formula of the lower contraction: (h c)_E(m) = (-1)^p c_(E+j)(m) for
  the selected j of m (0 if j in E), and 0 if all exponents of m are
  negative; outputs are elements of the chart modules (finite support and
  chart conditions proved, not only pointwise identities).

3.4 Top coordinates (TopList4, TopCoordinates4).
  T20: the quadruples (n_0..n_3) of naturals with sum 3 (a_i = n_i + 1,
  sum a_i = 7), top exponent topExp = (-a_0,..,-a_3).
    t20-length : len T20 = 20 (computation);
    t20-nodup  : no duplicates (decision procedure dec-nodup computes to
                 yes);
    exhaust    : sum n_i = 3 => member of T20 (generated case tree,
                 checked);  deg-allneg, top-mem : an all-negative
                 exponent of degree -7 is a top exponent.
  top : C^3(-7) -> D^20 (linear), top(w)_k = w_0123(-t_k).
  pi-expand : pi(w) = sum_k top_k(w) X^(-t_k)  (expand), pointwise.
  pi-zero   : top(w) = 0 => pi(w) = 0.
  The 2 x 20 matrix of (-Q, P) on top cohomology was not computed (the
  handoff marks it optional, and its kernel is not needed).

3.5 The certificate relation (CubicCertificate).  Z = Deg[mOne].C1 =
  C^1(-1) (all chart 1-cochains, not a quotient), V = D^20.
    E1 b u v : d b = P u + Q v             (u, v in C^2(-4))
    E2u u w  : d u = -Q w,  E2v v w : d v = P w   (w in C^3(-7))
    Gam(b,p) := || (u,v,w) * E1 * (E2u * E2v) * top(w) = p ||  (Witness)
    B(b)     := || (h, a_0, a_1) * b = (d h + P a_0) + Q a_1 ||  (Bdry)
  Raise[b,u,v,e1]: w = X_0^-3 (d v); rel (P du + Q dv = d d b = 0),
    ev (d v = P w), Pdu, eu (d u = -Q w), witness.  partner: a truncated
    E1-lift gives a truncated partner.
  gam-zero, gam-add (Add), gam-sm (Scale): linear closure.
  Reflect[b,x] (zero-reflection, PROVED): pi0 (pi w = 0), t = sigma w,
    dt (d t = w), u' = u + Q t, v' = v - P t, du' = 0, dv' = 0,
    a0 = con2 u', a1 = con2 v', da0, da1, c = (b - P a0) - Q a1,
    dc (d c = 0, using P Q t = Q P t), h = con1 c, dh, eqb, and the
    exported primitive bdry : Bdry b.  reflect: the proposition-level
    implication.  rel : RelationCertificate.Rel for this Gam and B.

3.6 FINAL THEOREM (CubicDependence.Over[K0,D,setD,cfn].Seq[b,lift].dependence).
  D a CFN set-ring, b : Nat -> C^1(-1),
    lift : (n : Nat) -> || (u_n, v_n in C^2(-4)) * d b_n = P u_n + Q v_n ||.
  Then  || (qs : List D) * (h in C^0(-1)) * (a_0, a_1 in C^1(-4)) *
            b_N - sum_{i<N} q_i b_i = (d h + P a_0) + Q a_1 ||,  N = len qs.
  No sequence of u_n, v_n, w_n is chosen: raising is applied under each
  single truncation (CubicCertificate.partner).  OverZ.dependence-Z: the
  instance D = Z (ZCFN.cfn).

3.7 Nonzero example (CubicExample), over any D:
  w = X_0^-1 X_1^-1 X_2^-1 X_3^-4 (exponent of tq = (0,0,0,3), i.e.
  a = (1,1,1,4)): wE in C^3(-7); uE (u_023 = Q w), vE (v_123 = P w),
  bE (b_23 = P Q w), each with its chart and support proved;
  e1 : d b = P u + Q v (explicit components); raises-w : the raising
  formula recovers exactly w; eu, ev : d u = -Q w, d v = P w; gam :
  Gam(b, top w); coord : top(w) at tq is 1; nonzero : 1 /= 0 => top(w)
  /= 0.  OverZ.nonzero-Z : over Z (one-ne-zero), top(w) /= 0.


4. VALIDATION
-------------
  timeout 55 ./segc sag/zmt-lifting all
      68 modules, 0 failed, 0.45 s, OK
  cd sag/zmt-lifting ; timeout 55 $(cabal list-bin exe:seg) All.seg
      All.seg: 3338 declarations, 0 failed, 0.89 s, OK   (real 0.90 s)
  ... All.seg --opens zmt-lifting.opens
      30 Stage 1 declarations: "nothing else opened" for each.
  Stage 1 gate (before Stage 2): RelationCertificate, CertifiedDependence,
  LinearCertificate checked fresh: 1737 declarations, 0 failed, 0.33 s.
  Mutation test: flipping one sign of cone2 makes htpy1, htpy2, van-h2,
  vanish-h2 fail; restored.

  New declarations (862), all checked; per file (max time per decl,
  max definitions opened by one decl):
    RelationCertificate   63   0.00 s     44
    CertifiedDependence   38   0.00 s     16
    LinearCertificate     21   0.00 s     21
    Laurent4             128   0.00 s     49
    Cech4                119   0.00 s    398
    Cech4Contraction      88   0.01 s   1957
    TopList4             104   0.00 s   1325
    TopCoordinates4       67   0.00 s    104
    CubicCertificate     149   0.03 s    948
    CubicDependence       22   0.00 s     13
    CubicExample          63   0.00 s     89
  Performance: no overrun.  The large opening counts are: (i) "by
  definition of the selected contraction" (sel, Signs, cone at each of
  the 5 sign branches: htpy*-sel, van-h*); (ii) the decision procedure
  of t20-nodup (190 comparisons, by computation, as stated); (iii) in
  CubicCertificate, the identification of the carriers and operations of
  different chart-module instances (Chart.mod / SubMod.mod record
  projections, and the twists mOne = suc3 mFour, mFour = suc3 mSeven,
  each one unfolding).  Defining the twists by suc3 halved (iii); writing
  the equalities at mod.M reduced it further.  These are representation
  costs, not hidden steps; no .opens is claimed for Stage 2.


5. HELPERS, CONSTRUCTED INSTANCES, OBLIGATIONS, SCOPE
-----------------------------------------------------
Generic helpers (usable elsewhere): RelationCertificate (Rel, reduce,
LinL), CertifiedDependence (the theorem for any Rel), Laurent4.Chart /
Restrict, Cech4Contraction.Signs.

Constructed (not parameters) in the cubic instance: the chart modules,
d, P, Q, X_0^-3, the contractions pi, sigma, con1, con2, the top map,
Gam with its linear closure, the raising, and the zero-reflection.  The
Stage 2 instance has no hypothesis carrying a conclusion: its only
parameters are D, setD and (for dependence) CFN.

Remaining obligations within the two stages: none.  Minor limits:
  * finite support is "vanishes outside a finite list" (with repetitions);
    a bridge to LaurentList's coefficient-list notion (coef of a term
    list) is not formalised;
  * the contractions are operations on elements (finite support and chart
    conditions proved), not packaged as linear maps (not needed);
  * the optional 2 x 20 consistency matrix is not computed;
  * Stage 2 .opens specifications were not written (see 4).

OUT OF SCOPE (not proved here): full ZMT; general finite-fibre lifting;
the Rees comparison; arbitrary projective dimension / arbitrary
homogeneous resolutions; the weighted/bigraded polynomial theorem needed
for full ZMT (future work); general syzygy or regular-sequence theorems
(the top syzygy (-Q, P) of this example is supplied by the explicit
raising formula); generation of the finite kernel of the top matrix.
The companion note's remark "No Unit check of this example is claimed"
is superseded by this development (the note itself was not edited).
