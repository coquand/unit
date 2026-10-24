Rank-one affine Horrocks, for any commutative ring
==================================================

HorrocksProof.Over[A,setA].horrocks : HorrocksInterface.Over[A,setA].Horrocks

The theorem holds for an arbitrary commutative ring A (with a set as
carrier). It uses no SAG axioms, determinants or Schanuel lemma. The only
global assumptions are those of the foundation: univalence and
replacement, with truncation and effective quotients derived
(see All.seg). It is used in ../picard for Proposition 4.6.

Check
-----
  "$(cabal list-bin exe:seg)" All.seg
    6128 declarations, 0 failed, 3.1 s (22 October 2026)
  cd ../picard && python3 check.py --isolated
    the whole Picard development from an isolated copy (see ../picard)

REVIEW-FILES.txt lists the files to review; SOURCES.sha256 and
DEPENDENCIES.txt record hashes. PROOF-TOOLS.txt describes the external
ring normaliser that generates some ring rearrangements as ordinary
checked proofs.

Structure
---------
The gluing step is one general lemma, LocalGlobal, for a comaximal
family of monoids S_1..S_m of A, an A-algebra B and maps B -> D_i that
invert S_i, clear denominators and have kernel killed by S_i:
  Ideal.member   an element of B lies in a finitely generated ideal
                 if its image does in every D_i;
  Overlaps.Glue  elements of the D_i that agree on all overlaps come
                 from one element of B.
HorrocksProof: local monic generators (LeafClearing), they agree on
overlaps (LeafOverlap), glue them, use Ideal.member for g in (y) and
for y_j in (g), and descend (CertificateDescent).

Main checked results
--------------------

MonicLifting.Over[A,C,setA,phi,lift-unit].At[...].lift
  Full monic lifting in a relative formulation. Given an ideal I of
  A[X], a monic f in I, and g in I whose image is monic of degree r,
  produce h in I monic of degree r with exactly the same reduction.
  The map phi must make every element mapping to 1 invertible.
  Polynomial bounds are explicit; no actual-degree decision is used.

FiniteRadicalLifting.Over[A,setA,m,fs].At[radical].Lifting
  Instantiates the preceding result with the actual quotient A/(fs),
  where (fs) is contained in the Jacobson radical. The kernel and
  unit-lifting conditions are proved, not assumed as extra axioms.
  This is the finite-ideal version needed at formal gcd nodes S(I;U).

LocalMonicGenerator.Over[A,setA,m,fs].At[...].Reduction[generates].factors
  Lemma 7.6 in the form needed for the row ideal of the existing
  scalar factorisation certificate. Given:
    * a finite Jacobson-radical ideal J=(fs) of A;
    * X_i Y_j=f^k E_ij and sum_i Y_i X_i=f^k, with f monic;
    * a monic h=sum_i Y_i hc_i;
    * coefficients a_i with Y_i=h*a_i modulo J[A[X]];
  merely produce coefficients b_i with Y_i=h*b_i in A[X].
  Its .free corollary returns the existing Free E type.
  This theorem uses no residual discreteness and needs no projector
  axioms beyond the supplied scalar factorisation certificate.

PolynomialNakayama...Given[...].all-zero
  If a ring receiving A[X] kills a monic h, and finitely many v_i
  satisfy v_i=sum_j q_ij(X)*v_j with every coefficient of each q_ij in
  a finite Jacobson-radical ideal of A, then all v_i vanish.
  The proof expands in the finite power basis, forms a rectangular
  finite family, and eliminates its generators over A.
  The degree-zero case is handled explicitly.

CertificateDescent.Over[B].At[...].descend
  A principal row ideal descends a scalar factorisation to Factors E
  whenever its scalar denominator is regular. It requires neither a
  trace calculation nor determinants.

MonicRegular...At[lower].power-regular
  The actual polynomial-ring element representing a monic, and every
  natural power of it, is regular. Degree zero and the zero ring are
  included. PolynomialMap proves preservation under base change.

LocalGlobal.Over[...].Ideal[...].member, .Overlaps[...].Glue[...].glue
  Local-global principle for comaximal monoids (see top of this file).

Global assembly
---------------

FormalGcd.compute
  The formal gcd tree over the monoids S(I;U). Each leaf carries a monic
  member of the row ideal that generates it modulo the leaf's radical.

FormalMonoidTree.comaximal, TreeLeaves.Partition.partition
  Any choice of one denominator per leaf generates the unit ideal.

PolynomialClearing
  Over a monoid localization A_S: polynomials times some s in S come from
  A[X]; a polynomial of A[X] vanishing over A_S is killed by some s in S.

LeafClearing
  At a leaf, Lemma 7.6 (LocalMonicGenerator) gives a monic generator of
  the row ideal over A_S[X]; the leaf's localisation map satisfies the
  three hypotheses of LocalGlobal (units, clear, kernel).

LeafOverlap
  For two leaves, over the product monoid S1 S2 both monic generators
  generate the row ideal, so they are equal (MonicUniqueness, including
  different degrees); the overlap map has kernel killed by S1 S2.

CompatibleNumerators
  r_i = prod_k u_ik v_ki, s_i = d_i r_i, H_i = r_i p_i satisfy
  s_i H_j = s_j H_i exactly; used inside LocalGlobal.Overlaps.Glue.

HorrocksProof
  Glue the local generators to g; g in (y) and y_j in (g) by
  Ideal.member; CertificateDescent cancels f^k.

The global generator g need not be monic. The leaf degrees may differ.
