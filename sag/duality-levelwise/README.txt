duality-levelwise: the three presheaf axioms of jonas.pdf §6.3 in the
presheaf model, read internally to cSet (reading (A) of DUALITY.md),
checked with Unit.  Plan and premise table: unit/sag-model/DUALITY.md.
Check: from unit/, ./segc sag/duality-levelwise all.

RESULT.  T3FromModel.PresheafAxiomsM: duality (Axiom 2, Thm 62),
n-constant (Axiom 3, Thm 61), projective (Axiom 1, Prop 76), with
no new axioms beyond the named premises:
  T2     S2.1-S2.8: the presheaf CwF, site, Pi, the cobar D, local
         representability, modal Pi (record fields of T2.seg)
  S36    S3.6: the site's objects are R-algebras, an object for each
         presented algebra (Construction 39, Lemma 42)
  S39    S3.9: N, List, Expr_G levelwise; points of G0 = syntactic
         presentations (P3.3)
  PModF  S3.1/S3.2: presented models in families, fibrewise reading of
         the model structure of <-> over G0 (ModelD of Transfer2 inside)
  SpF    S3.5 and S3.1: G, Sp (hom-type of models <u> -> G), ev
  Mods   S3.10: <-> and G D-modal, G and Sp fibrant
  NS     S2.7: N fibrant, modal, fibres ~ Nat
  TrS    S3.7/S3.8: truncation in the model, and Prop 34
         (El(U Gamma, ||U A||) <-> El(Gamma, ||A||))
and the ambient axioms of Axioms.seg (function extensionality,
univalence).  Tier 1 (the algebra) uses no premises.

FILES (-> = symlink; jonas.pdf numbers in brackets).

Tier 0, foundations (-> ../duality)
  Base, Prelude, Paths     data types, identity types, path lemmas
  Axioms, FunExtUA         funext and univalence; funext from univalence
  Replacement, Truncation, Quotient   replacement [Cavallo-Coquand], truncation, small quotients
  Equivalences             composition, homotopy, injectivity of equivalences
  SigmaEq                  equivalences of Sigma types (used by Prop 58)

Tier 1, commutative algebra (-> ../duality, no premises)
  Ring, RingHom            commutative rings, unital homomorphisms
  Poly, Mul, RawLaws, RawMultiplication, PolynomialRing   A[X] as a quotient ring
  Evaluation, Universal, Substitution   evaluation, universal property of A[X]
  Algebras                 R-algebras and their maps
  Presentations            finite presentations, solutions, Presents
  AddVariable, BasePresentation, FinSum   presentation constructions
  ExpressionCongruence, CongruenceSoundness, PresentedAlgebra,
  PresentationExistence    every presentation has a presented algebra
  PresentationComparison   presented algebras are unique up to iso
  Tensor, Pushout, BaseChange   coproducts, pushouts, base change [SAG 3.2.1-3.2.2]
  Generated                elements of a presented algebra are values of expressions
  Relative                 presentations over an algebra, change of coefficients [§6.4.1]
  RelativeChange           h+ : X_u -> X_{u.h} is a pushout [Lemma 50]
  Points                   retractions of p_w = solutions [Construction 57, base part]
  Representability, Presented   base part of Prop 58; chosen base changes

Tier 2, presheaf CwF (-> ../duality-presheaf)
  T2                       records PCwF, Site, PiS, DS, LocRep, ModPi (S2.1-S2.8)
  TE                       transport of elements; the relation TE; subExt; teAny (only use of isSetTy)
  Lemma66                  [Lemma 66]
  Lemma67                  [Lemma 67]
  Prop69                   the modal Yoneda lemma [Prop 69]
  Lemma72                  [Lemma 72 = Lemma 59]
  Remark60                 [Remark 60], at general LocRep

Tier 3, levelwise characterisation
  T3                       record T3: S3.5, S3.6, P3.3-P3.5 with the ev clause [Constructions 55-57]
  Transfer                 Lemma 52 generic: WCat, Adj, transfer, Yoneda iso, coequalisers [Lemma 52]
  Transfer2                presented models: FamB, ModelD, PresTr.brEq [Lemma 52, Cor 53]
  BrFromModel              S39, PModF; brE, brE-nat (P3.4) [Construction 56]
  OnFibNat                 maps of types on fibres commute with restriction (pairO, postNat)
  SpFromModel              SpF; spE, spE-eq, ev-clause (P3.5) [Construction 57]
  SpNat                    spE-nat (P3.5)
  P58Lemmas, P58           Sp locally representable [Prop 58]
  T3FromModel              S36; Build.t3 : T3 from S36, S39, PModF, SpF

Tier 4-5, the axioms
  Core                     heart of Theorem 62: q_u . p_u+ ~ id
  E1                       Axiom 2, duality [Thm 62]
  E2                       Axiom 3, N constant [Thm 61]
  E3                       Axiom 1, projectivity of Sp [Prop 76, Remark 71]
  SAGPresheaf              the three axioms from T3 (PresheafAxioms)
  All                      imports everything above

Not imported by All (symlinks into ../duality, SQC-side results not used
here): Functions, SpecMaps, SqcTensor, Vanishing, CoefficientBound,
BoundedCorollary, Examples [SAG 3.2.2-3.3.3].

Authors: design Thierry Coquand; code Claude (sessions canonicity-4e,
canonicity-45).
