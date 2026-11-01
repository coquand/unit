DIRECT FLAT + UNRAMIFIED => ETALE
31 October 2026

1. Status and exact theorem

The arbitrary-base theorem is proved and checks. For any commutative
set-ring R and R-algebra E, finite presentation, R-flatness and formal
unramifiedness imply unique lifting across every square-zero quotient.
There is no local-ring, residue-field, prime, ZMT, coherence, decidable
equality, characteristic or dimension hypothesis.

The endpoints in FlatUnramifiedEtale.Over[R,setR] are:

  At[T,fp,unramified,flat].formally-etale : FormallyEtale T
  At[T,fp,unramified,flat].lift           : Lift T
  At[T,fp,unramified,flat].etale          : ||Etale T||

Here fp : Presentations.FP T is a merely given finite presentation;
unramified : FormallyEtale.Unique T; and
flat : FlatRelations.Over[R,T.ring,T.iota].Flat.
The last conclusion is truncated because Etale contains an actual
presentation witness. The lifting function itself is not truncated.

  Presented[T,presentation,unramified,flat].theorem : Etale T

This explicit-presentation version takes presentation : P.Witness T
and returns the existing, untruncated definition of Etale. Thus no
interface has been weakened or renamed to obtain the conclusion.

Unramified means the existing uniqueness-of-square-zero-lifts predicate.
This development does not prove its equivalence to a different definition
using Kahler differentials.

2. Proof and intermediate exports

FlatQuotientLift.Over[R,setR].At[S,T,u,surj,flat,smooth].lift:
  Formal smoothness descends through a surjective flat algebra map.
  The existing FlatQuotient theorem gives z=z*b with b in ker u for
  every z in ker u. A lift into B with square-zero ideal N sends both
  factors into N, so sends z to zero. EtaleCase.Surjection.Factor
  constructs the descended algebra map. No finite generation of ker u
  or idempotent generator is needed.

ExpressionJets:
  Directional differentiation and first-order Taylor expansion of finite
  polynomial expressions, for any variable set. Finite gradients come
  from linearity and the existing finite linear-form expansion theorem.

FreePolynomialJets:
  Differentiation on the actual free polynomial algebra is constructed
  by its universal map into QuadraticPairs at parameter zero (dual
  numbers). The constant/linear components and product rule are proved.
  No differentiation of quotient representatives is postulated.

JacobianTools and JacobianLifting:
  Finite equation families, gradient/determinant naturality and linear
  solving by the existing right adjugate. For n equations in n variables,
  construct the presented algebra and invert its Jacobian determinant.
  One Newton correction proves lifting. The adjugate proves uniqueness.
  Every representative is selected under truncation and unique lifting
  makes the target proposition-valued. The n=0 case is included.

DiagonalJacobian.Over[R,setR,E,p,pe].Unramified[unique].theorem:
  Merely a matrix C with C*J=I, where J is the Jacobian of the ORIGINAL
  equations of p at the given generators of E. The number of equations
  is arbitrary; zero and redundant equations are allowed.
  Construct Q=E[Y], map the original coefficients into it, and form the
  effective quotient by those finitely many equations. Map the checked
  diagonal tensor certificate into this quotient. Its image has value
  one on the diagonal and equalises the two E-maps. Lift it to q in Q.
  Effectiveness gives finite witnesses for q*(Y_i-x_i) in the equation
  ideal. Differentiate them at Y=x. This gives C*J=I.
  FiniteEquationQuotient supplies the effective quotient and its maps;
  MappedJets proves differentiation commutes with coefficient change.
  PresentationKernel is reused for its equation-indexing helpers, not
  for its main kernel theorem; the explicit quotient provides the
  needed kernel certificates directly.

UnramifiedEtaleSource.Over[R,setR,E].theorem fp unique:
  Merely a constructed finitely presented formally etale S, an R-map
  S -> E and mere surjectivity. Lift the coefficients of C and set
  F_i=sum_j Ctilde_ij*f_j. Their Jacobian equals I in E, so its determinant
  maps to 1. Apply JacobianLifting to S=(R[X]/(F))[1/det J_F].
  No flatness is needed for this intermediate theorem.

FlatUnramifiedEtale:
  The existing general FlatDiagonalTransfer gives S-flatness of E.
  Apply FlatQuotientLift. Formal unramifiedness of E gives uniqueness,
  so the merely constructed source is eliminated into each unique lift.

3. Regressions and mutations

DirectRegression checks:
  - The empty presentation over every commutative set-ring, including
    the zero ring, through the new final endpoint.
  - The presentation X=a of the base algebra; also the redundant
    presentation (X-a, 2*(X-a), 0), which exercises a rectangular
    Jacobian. Instantiated at a=2 over Z/4Z.
  - R[1/t] over every base R. Flatness is supplied by the existing
    localisation theorem; unramifiedness comes from the universal
    property, without using the new lifting result. Instantiated for
    t=1 and the nilpotent t=2 over Z/4Z.
  - The nonsymmetric two-variable Jacobian of (X+Y,Y) over Z/4Z.
    Its determinant is 1; the right-adjugate solver sends (0,1) to
    (3,1), and both resulting equations are checked.

Three isolated mutations were rejected:
  - positive instead of negative Newton correction;
  - sums instead of products in the linear combinations of equations;
  - transposing the nonsymmetric regression Jacobian.
The mutations were made only in temporary copies, never in the working
proofs or shared files.

4. Validation and checking

Fresh built-checker All.seg --opened:
  5834 declarations, 0 failed, 2.26 s.
  557 owned declarations/events in 11 new proof modules.
  Every owned declaration <= 0.02 s, at most 32 distinct definitions
  opened. Nineteen open directives are included in the event count.

./segc sag/etale-direct all:
  147 modules, 0 failed, 2.05 s.

etale-direct.opens covers all 538 named owned declarations.
Fresh --opens: all 538 report "nothing else opened";
  5834 declarations, 0 failed, 2.74 s.
The spec is a frozen audit of the actual openings, including concrete
quotient carrier/operation aliases. It is not a claim that only abstract
mathematical operation names unfold. The full check checks every proof.

Commands from unit/:
  ./segc sag/etale-direct all
  ./segc sag/etale-direct check FlatUnramifiedEtale DirectRegression
  cabal list-bin exe:seg
  <built-checker> sag/etale-direct/All.seg --opened
  <built-checker> sag/etale-direct/All.seg \
    --opens sag/etale-direct/etale-direct.opens
  ./segc sag/etale-direct stop

5. Assumptions and boundary

All.seg has only the usual univalence, replacement and surjection
parameters. There are no new axioms, checker modifications, or shared
proof-file changes. All reused proof modules are relative links. The
local/ZMT candidate construction and field structure developments are
not imported. Nothing is committed.

The constructed source is multivariable Jacobian etale. This development
does not provide a finite cover by monic ONE-VARIABLE standard etale
charts. That stronger structure statement remains separate. It does
prove flat + formally unramified => formally etale with finite
presentation, globally over the original base.

Mathematics first, formalisation correspondence second:
  ../../doc/etale-direct-analysis.tex (and the compiled PDF).

Further analysis, with the local shortcut now checked separately:
  ../../doc/etale-monic-cover-analysis.tex (and the compiled PDF).
It removes the gcd/Nakayama relation-lowering loop after local monogenic
generation: unramifiedness gives H(y)=0 with H'(y) a unit, and
H+T^(length H)*Q0^2 is a simple monic relation. This local shortcut,
including finite kernel generation and kernel removal, is now checked
in ../etale-monic-local; see its README and ShortLocalEtale.seg.
The note also gives a
direct cover by at most 2n^2 monic standard charts for
(R[X]/f)[1/f'] when n >= 2 bounds the degree of f, using Horner matrices,
cofactors and finite radical-ideal certificates. The several-variable
cover remains a separate problem. The matrices and finite-cover
certificates remain mathematical proofs in the note; their formalisation
was outside the requested local-shortcut milestone.
