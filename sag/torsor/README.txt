SAG Section 7.4 (Cherubini, Coquand, Hutzler) in the primrec prototype
======================================================================

Check from the repository root:   ./segc sag/torsor all          (1556 declarations, 1.1 s)

Contents: Lemma 7.4.2 (torsors), Theorem 7.4.7 (gerbes), Theorem 7.4.8
(Cech H^2 = gerbes, as abelian groups, compatible with refinement), and
Lemma 7.3.5 / Theorem 7.3.6.

Statement (Tors.lemma-7-4-2): for an abelian group A and L with ||L||,

    (T : A-torsor) * (L -> T)   ~   L-cocycles   (c i j + c j k = c i k)

as an equivalence (qinv) with explicit inverse c |-> (T_c, i |-> c i -),
T_c = { v : L -> A | v m = v k + c k m }.

A-torsor: a set T with an action (a+b).t = a.(b.t), 0.t = t, free and
transitive (each  a |-> a.t  has contractible fibres over t'), and ||T||.

Hypotheses: those of ../replacement/All.seg only (univalence, replacement
as images + surjectivity); funext and ||-|| are derived there.  Univalence
is used once, as induction on equivalences (eqind), to turn the equivariant
bijection  t |-> (k |-> t - u k)  into an identification (sip).  ||L|| is
eliminated only into propositions (contractibility), as in the paper.

Base, Prelude, Paths, Axioms, FunExtUA link to ../core; Replacement and
Truncation link to ../replacement (not modified).

SAG Theorem 7.4.7 (gerbes)
==========================

M74.theorem-7-4-7 (Gerbe74.seg): for A abelian and L with ||L||,

    (G : A-gerbe) * (u : L -> G) * ((i j : L) -> u i = u j)  ~  L-2-cocycles

with c i j k = beta (p i j . p j k . (p i k)^-1) and the cocycle law in
the form  c i j k + c i k m = c j k m + c i j m.  Gerbes are in U l, as
in SAG.  Hypotheses: those of All.seg only (no SAG axiom).

A gerbe (Gerbe.seg): a 1-type (torsor3.pdf), merely inhabited, connected,
with for each x a band  beta_x : (x = x) -> A  that is a group iso (given
by contractible fibres).  The compatibility of the bands with
conjugation is a lemma (band-conj), not a field.

Proof.  Being an equivalence is a proposition, so assume i0 : L.
  TorsorId      torsor paths are equivariant maps; Aut X = A
  Gerbe         paths form torsors; band-preserving maps are equivalences
  Cocycle2      the map to 2-cocycles and the cocycle law
  TrivialGerbe  the torsors form the trivial gerbe; its small version K
                is the image of the point A (replacement)
  Trivialise    G ~ K by y |-> torsor of paths u i0 = y; points go to the
                base point, paths to the loops of band c i0 i j
  Sip2          structure identity for gerbes with points and paths
  Gerbe74       fibres contractible: centre the trivial gerbe with those
                loops, contraction by Trivialise and Sip2
Deligne's general gerbe of a cocycle is not needed: with a point, every
gerbe with points is identified with the trivial one.

Coboundaries (Coboundary.seg), towards SAG Theorem 7.4.8
--------------------------------------------------------
For a gerbe with points and paths (G, u, p) with cocycle c:
  Cob.Change[b].thm      replacing p i j by  b i j . p i j  gives the
                         cocycle  c + delta b,  delta b i j k = b i j + b j k - b i k
  Cob.Objects.theta-equiv   for ||L||:
      (y : G) * ((i : L) -> u i = y)  ~  (b : L -> L -> A) * (c + delta b = 0)
      theta (y, r) i j = the difference from p i j to r i . (r j)^-1
The paths r are data, so nothing is chosen; a point of L is assumed only
to prove that theta is an equivalence.  So c is a coboundary iff merely
there is an object with paths to all the u i.

SAG Theorem 7.4.8 (Cech.seg)
============================
Setting (Cech): X, a finite cover U 1 .. U n (every x merely in some U i),
F : X -> Ab.  L x = (i : Fin n) * U i x; Cech 2-cocycles are
(x : X) -> L x-2-cocycles; Gc c is the family of gerbes given at each x by
the inverse of Theorem 7.4.7; Rel c c' says c' = c + delta b.
2-acyclicity by sections: TorsAcyc i j (families of torsors over
U i n U j, including i = j) and GerbeAcyc i (families of gerbes over U i)
merely have sections.

Thm.well-defined   Rel c c' -> Gc c = Gc c'
Thm.injective      || Gc c = Gc c' || -> || Rel c c' ||
Thm.surjective     every family of gerbes G : || (c : Z2) * Gc c = G ||
Together: c |-> Gc c is a bijection from Cech classes onto
H^2(X, F) = || (x : X) -> F x-gerbe ||_0, stated without quotient types.
Finite choice (fc, by recursion on n) chooses the local objects and the
paths on all U i and U i n U j at once.  The group structures and
acyclicity as vanishing are below.

Acyclicity as vanishing, and the quotient equivalence
-----------------------------------------------------
Vanish.seg      a torsor has an element iff it is A; a gerbe has an object
                iff it is K (trivialisation with one point, Sip2 with none)
Cech.Thm2       the comparison with SAG's acyclicity: H1Zero i j (every
                torsor family over U i n U j merely equals the trivial one)
                and H2Zero i (every gerbe family over U i merely equals K);
                both are shown equivalent to the section form
CechQ.theorem-7-4-8 : Hc ~ H2, an equivalence of sets, where
                Hc = Cech 2-cocycles / merely cohomologous,
                H2 = || (x : X) -> F x-gerbe ||_0  (quotient by mere equality),
                with the quotients of projective/Quotient.seg (linked).

Addition (TorSum, GerbeSum, SumCocycle, CechQ)
----------------------------------------------
TorSum      sum of torsors T (x) S as the centre of the contractible type of
            bilinear maps (torsor3 2): q (a.t) (b.s) = (a+b) . q t s,
            Hom (T (x) S) Z ~ BiHom T S Z, functoriality
GerbeSum    sum of gerbes: image of  g |-> (h |-> (h1 = g1) (x) (h2 = g2));
            band = constant value of the pointwise torsor bands (cinv);
            mu-band: beta (mu (l1, l2)) = beta l1 + beta l2
SumCocycle  the cocycle of the sum system is c + d
CechQ       Gc (c + d) = Gc c + Gc d (equality of families); addHc, addH2 by
            descent; m-add: the equivalence theorem-7-4-8 preserves addition
CechGroup   zero, negation and the group laws on Hc (pointwise on cocycles);
            zero of H2 = class of the trivial family (m-zero: the zero
            cocycle is realised by the trivial gerbe, constant points,
            identity paths); laws of H2 for the gerbe-sum addition,
            transferred through m.  CG.iso: Hc ~ H2 as abelian groups.

Refinement (Refine.seg)
-----------------------
Ref: a finite cover V refining U through rho : Fin n' -> Fin n with
V j x -> U (rho j) x.  Cocycles pull back along (j, v) |-> (rho j, v).
  Gc-pull           the gerbes of the pulled-back cocycle are the same
                    family (restricting points and paths pulls back the
                    cocycle), an equality
  Classes.natural   m_V (refine q) = m_U q  for 2-acyclic U and V
  Classes.refine-add, Indep.indep   refine is additive and does not depend
                    on rho
  RefId.refine-id, RefComp.refine-comp   identity and composition laws
Any two 2-acyclic covers are compared canonically through H2.  A common
refinement receives the two Cech refinement maps without any acyclicity
(pullZ and rel-pull use none); acyclicity of the refinement is needed only
for its own comparison map to be an isomorphism.  Here Hc is built inside
CechQM, which assumes acyclicity, so Ref.Classes states refine for
2-acyclic covers.

SAG Lemma 7.3.5 and Theorem 7.3.6 (Alg73, Affine)
-------------------------------------------------
Alg73.seg   rings, modules, finite sums over Fin n, common bounds of
            finitely many numbers.  L735.lemma-7-3-5: for an A-module M,
            f 1 .. f n with sum r k f k = 1, s i j = m i j / (f i f j)^N
            with s j k - s i k + s i j = 0 in M_(f i f j f k) (killed by a
            power, FEq/Zero on representatives), there are p, V with
            V i / (f i)^p - V j / (f j)^p = s i j  in M_(f i f j).
            Steps: synchronisation of the exponents (bound3), powers of
            unimodular elements are unimodular (Reg.pow-unim, geometric
            series), and the computation Core.key:
              F j V i - F i V j = mu i j,   V i = sum rho k mu i k.
Affine.seg  Aff.Thm.theorem-7-3-6: every M-torsor T on X merely has a
            section.  R a ring, X a type, M x R-modules, functions X -> R
            in place of A, D(g) x = "g x is a unit".  Hypotheses (Aff):
              LocR     1 /= 0, a + b unit -> merely a or b unit
              ZChoice  inhabited families merely have sections over the
                       D(f k) of unimodular f 1 .. f n
              WQC      M(X)_g = M(D(g)) on elements: sections over D(g)
                       are merely m / g^N; a global m vanishing on D(g)
                       is merely killed by a power of g (Lemma 7.1.8, U = X)
            Proof: local sections s i (Z-choice), differences t i j as
            m i j / (f i f j)^N (WQC, finite choice, bound), the cocycle
            numerator vanishes on D(f i f j f k) hence is killed by a power
            (WQC), Lemma 7.3.5 at each point x with R and M x, corrected
            sections (-u i) . s i agree on overlaps and glue (Lemma 1.2.2,
            the D(f i) cover X by Loc).
Paper: the u i of 7.3.5 satisfy s i j = u j - u i, while the proof of 7.3.6
uses t i j = u i - u j (replace u i by -u i); "M(U i n U j)_(f i f j)" there
should read M(X)_(f i f j).
