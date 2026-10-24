SAG Section 4.1: closed subtypes, and Lemma 1.3.8
================================================

Worker A. Dependencies in affine/, presentations/, tensor/ and opens/ are
read-only symlinks; the checker and those files have not been changed.

From the repository root:
  ./segc sag/closed all

Independent checks without a server or --only:
  checker=$(cabal list-bin exe:seg)
  (cd sag/closed && "$checker" All.seg && "$checker" Section4.seg)

All.seg checks Section 4.1 and dependencies.
Section4.seg additionally checks Worker B's Section 4.2 files from opens/.
Both use the same ClosedProp module. No namespace copies or extra axioms
are needed for their integration.

Foundation: the existing univalence and replacement parameters. Truncation,
effective quotients and function extensionality are derived. Geometric
axioms remain explicit parameters, with the SAGAxioms interface of Section 3.
Nothing here interprets these axioms in a model.

4.1.1: ClosedProp.seg
--------------------
ClosedProp[l].Over[R,setR] exports
  Zeros n xs = (i : Fin n) -> xs i = 0;
  Witness Q = (n : Nat) * (xs : Fin n -> R) * Equiv Q (Zeros n xs);
  Closed Q = || Witness Q ||;
  ClosedSubtype X sub = (x : X) -> Closed (sub x).
Closed-prop recovers isProp Q; equivalences in witnesses ensure that
nonpropositional types are not accidentally classified as closed.

4.1.2 and 4.1.3: ideals and closed loci
-------------------------------------
Ideals.seg defines an ideal as a proposition-valued predicate with its
zero, addition and scaling laws. Finite generation is mere existence of
a finite family with the same membership predicate. GeneratedIdeal.seg
uses truncated explicit linear-combination certificates.

ClosedInclusion.seg proves, with uniform SQC:
  V(fs) contained in V(gs) iff every g_j belongs to the ideal (fs).
The proof uses SQC on A/(fs) to detect vanishing, and quotient
certificates to recover actual ideal membership. It does not replace
ideals by their radicals, and needs no Loc hypothesis.

ClosedIdeals.seg proves an equivalence between finitely generated ideals
of R and closed propositions, with both order-reversal implications.
The forward map sends J to "every member of J is zero". Its inverse is
the ideal {a | Q -> a=0}. This constructs the ideal directly, without
selecting a finite equation witness from a truncation.

ClosedOrder.seg supplies the literal paper formulations:
- both orders are partial orders on sets;
- vanishing of J is equivalent to equality J=(0);
- generatorwise inclusion is equivalent to inclusion of entire ideals;
- the equivalence of 4.1.2 reverses the orders;
- 4.1.3 is stated with literal ideal inclusion.

Pure algebra: denominator clearing and Lemma 1.3.8
-------------------------------------------------
LocalizationKernel.seg, using only the canonical universal property:
  a/1=0 in A_f iff || (k : Nat) * f^k*a=0 ||;
  a/1=b/1 iff || (k : Nat) * f^k*a=f^k*b ||.
The proof extracts a polynomial certificate in A[Y]/(fY-1) and applies
the coefficient calculation LinearPolynomialCertificate.annihilate.

LocalizationIdeal.seg:
  a/1 belongs to (g_i/1) iff || (k : Nat) * f^k*a belongs to (g_i) ||.
It uses an explicit quotient and a localization model; no SQC, Loc,
finite presentation of the source, or assumed saturation theorem.

LocalizationOverlap.seg proves that (A_fj)_{fi} has the canonical
universal property of A_{fi*fj}. It records the maps from both local
algebras and their agreement on A.
LocalizationFinite.seg derives finite presentability of ANY localization
with the UP when its source is finitely presented. Thus the FP field in
localization witnesses is not an additional algebraic assumption.

IdealGluingFinite.seg and IdealGluing.seg:
  clear each numerator generator against every other local ideal;
  combine finitely many exponents;
  concatenate the generators after multiplying them by these powers.
IdealGluingFractions.seg first replaces arbitrary local generators by
numerators, without changing their ideals.

IdealGluingRing.seg specializes the base ring to A itself. Every ring is
finitely presented over itself, so A is arbitrary.
IdealGluingIdeals.seg defines ideal extension independently of a choice
of generators and proves gluing for local finitely generated ideal
predicates.

Exact equality interface:
  IdealGluingEquality[l].Over[A,setA].At[m,fs,ls,js,os].lemma-1-3-8
Given equality of the extended local ideals on the iterated overlaps,
it produces merely a global finitely generated ideal whose extensions
equal the prescribed ideals. Neither a covering assumption nor a
geometric axiom is required. There is no uniqueness claim without a cover.

4.1.4: ClosedLocal, ClosedGlobal and ClosedAffine
------------------------------------------------
ClosedLocal.seg applies Z-choice to finite equation witnesses.
UniformBounded bounds their lengths on each localized spectrum;
ClosedLocalPad.seg pads with zeros, and SQC converts the coordinate
functions into elements of the local algebra.

ClosedGlobal.seg derives compatibility on overlaps from 4.1.3 and the
equality of their maps back to A. It applies ideal gluing and uses the
finite cover to identify the resulting global zero locus with the
original subtype. Compatibility is proved, not a hypothesis.

ClosedAffine.Over[R,setR,axioms].At[A,fp,sub,closed].theorem produces
merely:
  finite elements gs of A;
  a finitely presented quotient Q=A/(gs), with its universal property;
  an equivalence (sum x:Spec A. sub x) = Spec Q;
  proof that this equivalence lies over Spec A.
The separate theorem `affine` inhabits the Section 3 Affine predicate.
ClosedAffineGeneral.Over[R,setR,axioms].theorem handles an arbitrary
affine type X, via its proved unique affine representation.

Hypotheses: Loc, uniform SQC and Z-choice, finite presentability of A,
and pointwise closedness of the subtype. There is no choice over points
of X and no choice of presentation outside propositional truncation.

Regressions and review
----------------------
GlueExamples.seg covers the empty local family (so no hidden cover
hypothesis), localization at one, localization at zero, and ideal
membership after localization at zero.
ClosedExamples.seg uses dual numbers: epsilon^2=0, but epsilon is not
in the zero ideal. Under SQC, V(0) is consequently not contained in
V(epsilon). This tests the distinction between ideals and radicals.
Five new deliberately invalid assertions are rejected in #fails blocks;
five further expected rejections come from dependencies.

Independent read-only reviews checked 4.1.1--3, the overlap directions,
generator independence, exponent bounds, empty-family cases, truncation
eliminations and the equivalence over Spec A. Exact check results are
recorded in CHECKED.txt. Nothing is committed.
