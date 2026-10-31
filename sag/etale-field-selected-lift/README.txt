Selected factor to the local etale theorem
=========================================

Status: complete generic lifting bridge, checked 2026-10-31. This directory
does not prove that a selected primitive factor exists. Its input is a
supplied SelectedFactorStatement.Selected on the actual localized special
fibre. No shared source, earlier development or checker was edited. Reused
files are relative links. Nothing was committed.

1. Main export

SelectedLocalLift.Over has the same local-ring, prime, finite B, localization,
finite presentation and flatness parameters as SelectedFlatLocal.Over, plus
propositional membership of the base ideal m. Define:

  F = SelectedFibreLift.Over[A,setA,ideal,prop-m,algebraB,s]
  k = A/m = F.K
  C = (B/mB)[1/s] = F.Q.T.

These are the existing QuotientFibre quotients and PowerLocalization, with
their actual maps. No injectivity of B/mB -> C, B -> E, or B -> C is assumed.

GivenInverse[N,v,relation] takes the explicit quasi-inverse relation

  s^N (1-s*v) in mB

where membership is QuotientFibre.InIE (truncated finite witnesses).
Its Given[n,basis,prime,selected,prime-map] takes:

  - an actual finite k-basis of C;
  - a specified decidable proper prime of C;
  - SelectedFactorStatement.Selected[n,basis,prime] in C;
  - prime-map: q(j(b)) -> prime(eta(b)), for b in B.

The prime-map is only the needed direction of the preimage law. It remains
an explicit compatibility hypothesis; this module does not construct the
prime on C from q.

Exports:

  selected-data : || SelectedFlatLocal.SelectedData ||
  theorem       : || FlatLocalStatement.Conclusion ||

The latter calls the already checked finite selected local theorem. It is
conditional on the explicitly listed local inputs and selected field
certificate; it is not an unconditional flat+unramified theorem.

2. Exact equations and denominator handling

The supplied selected certificate has e, x, w, a monic coefficient list,
and polynomial representations of the finitely many basis elements of C.
SelectedPolynomial extends those representations explicitly to eta(bs_i).

QuotientPowerClearing.QuasiInverse.onto lifts e, x and w themselves into B.
In particular x is not replaced by s^a*x. FiniteListLifting lifts the root
polynomial and the finitely many representation coefficient lists through
A -> A/m, inside truncation. All Horner and derivative evaluations commute
with the two coefficient and target maps by PolynomialNaturality.

The resulting equations in C are pulled back using QuotientPowerClearing:

  s^a e P(x)                         in mB,
  s^b e (P'(x)w-1)                  in mB,
  s^c_i e (bs_i-C_i(x))              in mB.

The exponents may differ and are retained. Root and separability witnesses
are then mapped along j:B->E, including the power-map identities. The
generation equations remain in B. This gives exactly SelectedFlatLocal's
PRoot, PSeparable, PGenerates and Piece.

SelectedFlatLocal performs its existing refinement s'=s*e and consumes
the Piece unchanged. The image equation eta(e)=selected.idempotent and
prime-map give q(j(e)) false. Idempotence of the lifted e in B is not asserted
or needed by the local Piece interface.

3. Source modules

PolynomialNaturality.seg
  Horner naturality for a square of ring maps; constructs the induced map
  on dual-number rings and derives slope naturality. Includes the same-base
  specialization used to move B-equations to E. No derivative axiom.

FiniteListLifting.seg
  Merely-surjective coefficient maps lift one finite list, and finite
  indexed families of lists. No global representative selector.

SelectedQuotientLift.seg
  Generic core over QuotientPowerClearing[B,J,propJ,s], with a supplied
  coefficient ring map A->K, its surjectivity, K->C and commuting square.
  Given a supplied selected certificate, returns lifted elements/lists and
  all finite powered J-witnesses, under truncation.

FibreIdealWitnesses.seg
  Explicit conversions in both directions between finite-indexed IEWit
  and IdealGenerated's finite lists. Mere versions retain truncation.

SelectedFibreLift.seg
  Canonical specialization K=A/m and J=mB. Constructs the coefficient map,
  square and coefficient surjectivity from QuotientFibre. Converts only the
  finitely many resulting ideal witnesses to actual lists under truncation.

SelectedLocalLift.seg
  Exact Piece adapter, prime compatibility, and application of the local
  flat theorem. SameCoefficients transports root and slope to E.

SelectedLiftRegression.seg
  Full concrete regression described below.

4. Regression

Take A=E=F2, B=F2 x F2, m=(0), j first projection and s=(1,0).
The finite spanning family of B is (1,0),(0,1). The actual quotient and
localization C=(B/mB)[1/s] are constructed. Quotient descent followed by
the localization mapping-out construction gives C->F2; the scalar map
k=F2/(0)->C is proved to have an inverse. This supplies a rank-one basis.

The regression then constructs an actual prime of C and selected
certificate e=1, x=0, P=X, derivative inverse=1, representation of the
single basis vector by the constant polynomial 1. It applies the entire
canonical lift and exports both selected-data and the final local theorem.

Two additional checked facts are central:
  - the class of (0,1) is nonzero in B/mB;
  - its image is zero in C.
Thus the tested input really has a noninjective quotient-to-localization
map. The proof never transfers an equation through an assumed inclusion.

5. Validation

Commands from unit/:

  ./segc sag/etale-field-selected-lift all
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-lift/All.seg --opened
  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-field-selected-lift/All.seg \
    --opens sag/etale-field-selected-lift/etale-field-selected-lift.opens

Fresh All.seg: 14930 declarations, 0 failed, 7.07 s.
segc all: 335 modules, 0 failed, 6.23 s.
Seven owned modules: 351 declarations, including 14 open directives.
All 337 named owned declarations have opens specifications; every one
reports "nothing else opened". Maximum per owned declaration: 0.14 s and
26 definitions opened. The 0.14 s declaration is the concrete regression's
back-scalar quotient elimination; generic proofs take at most 0.01 s in
this fresh run. No shared abstraction was changed to improve these costs.

Two isolated mutations were rejected and did not touch working sources:
  - dropping the clearing factor s in the concrete quotient comparison;
  - replacing the dual-number derivative direction 1 by 0.
All checker invocations had a 60-second external bound. Audit logs:
  /private/tmp/etale-field-selected-lift-opened.log
  /private/tmp/etale-field-selected-lift-opens.log
  /private/tmp/etale-field-selected-lift-mutation-power.log
  /private/tmp/etale-field-selected-lift-mutation-derivative.log

6. Remaining integration obligations

The selected primitive certificate, its finite basis and compatible prime
must still be supplied on C. The quasi-inverse relation and the local ZMT
input remain explicit inputs. No global residue-field decomposition, no
primitive-element existence theorem and no global ZMT theorem are proved
in this adapter. Monicity is supplied by Selected but the local Piece only
uses the lifted equations; this directory does not separately export a
monicity proof for the arbitrary chosen coefficient-list lift.

The All.seg import closure includes the existing fibre and field trees
because QuotientFibre currently lives with the descent imports. This is
proof reuse, not additional hypotheses on the lifting theorem. The only
foundational parameters are the existing All.seg univalence, replacement
and surjection parameters.
