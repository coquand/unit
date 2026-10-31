LOCAL FLAT + UNRAMIFIED => ETALE
2026-10-31

1. Status and precise scope

The local theorem checks.  Given the local ZMT data and the shared
residue-field structure described below, a finitely presented, R-flat
algebra E has a standard etale neighbourhood at the specified prime q.
The neighbourhood also satisfies FormallyEtale.Etale: it is finitely
presented and has unique lifting across every square-zero quotient.
No lifting-existence hypothesis on E is used.

This is a theorem with explicit inputs, not a proof of the residue-field
structure theorem or an unconditional theorem over an arbitrary base.
No global version of ZMT is imported or invoked.  The local ZMT data
remain parameters.  The dynamical passage to a finite cover over an
arbitrary base is outside this directory.

All additions are isolated here.  Reused modules are relative links;
no shared/checker files were edited.  All.seg
has the existing univalence, replacement and surjection parameters; no
new axioms are introduced.

2. Why the flatness transfer theorem proves the desired last step

The existing local candidate construction supplies

    S --u--> T = E[1/g1],      g1 outside q,

where S is standard etale over R, u is surjective, and ker u is finitely
generated.  Unramifiedness is used through the residue-field data in
constructing this candidate.  Finite presentation gives the finite
kernel generators.  Since E is R-flat, so is T.

The new general transfer theorem says that, for any standard etale
R-algebra S and any R-algebra map S -> T, R-flatness of T implies
S-flatness of T.  This theorem itself uses no local ring, prime,
residue field, ZMT or unramifiedness hypothesis on T.

For a surjective flat map u, every x in ker u merely has b in ker u
with x = x b.  Thus I = I^2 for I = ker u.  The existing determinant
argument for a finitely generated idempotent ideal produces an
idempotent e with I = (e).  Consequently

    T = S/I is isomorphic to S[1/(1-e)].

The existing standard-localisation construction makes T standard
etale.  In geometric terms Spec T is an open-and-closed part of Spec S.

This replaces the special-fibre injection/Nakayama ending in Section
"What happens if E is flat and unramified" of zmt2-revised.tex.
In particular, no special-fibre isomorphism S/mS -> T/mT is needed by
this ending, and T needs no further localisation.

3. Main exports

FlatStandardTransfer.Over[A,setA].At[q,g,S,T,st,u,flat].theorem
  Input: st : StandardEtale.Points[q,g].Standard S,
         u : an A-algebra map S -> T,
         flat : FlatRelations.Over[A,T.ring,T.iota].Flat.
  Output: FlatRelations.Over[S.ring,T.ring,u.1].Flat.

FlatQuotient.Over[S,T,u,surj,flat].theorem x hx
  For hx : u(x) = 0, gives merely b with u(b) = 0 and x = x b.

FlatBaseStandardQuotient.Over[A,setA].At[...].theorem
  Takes S standard for (q,g), its polynomial-fraction representation
  (Full), a surjection u : S -> T, R-flatness of T, and finitely many
  proved generators of ker u.  Gives merely F with T standard for
  (q,g F).  It composes the transfer theorem, FlatQuotient and the
  existing EtaleCase.Section2.Localised construction.

StandardEtaleLift.Over[A,setA].At[q,g,S,st].formally-etale
  Gives unique square-zero lifting for every standard S.
  The export .etale additionally takes a finite presentation of S.

FlatLocal.Over[local ring, prime, local ZMT data].Field
  [x0,F0,presentation,flat].theorem
  Takes a single residue-field factor already selected at q.

FlatTheoremLocal.Over[local ring, prime, local ZMT data,
  presentation,flat].theorem
  Takes merely FieldData, selects a factor outside q, and returns
  merely FlatLocalStatement.Over[A,setA,E,setE,iota,q].Conclusion.

  Conclusion consists of s outside q, an R-algebra T and map E -> T,
  the universal property T = E[1/s], polynomials Q,G with T standard
  for (Q,G), and FormallyEtale.Etale T.  Standard is the existing
  points/universal-property API.  It does not separately export a
  monicity witness for Q.

  .theorem-of takes untruncated FieldData instead.
  .from-unramified takes Unique E and an explicit principle
       Unique E -> ||FieldData||.
  This last principle is the interface for the assumed shared
  residue-field result, not a theorem established here.

4. The explicit local and field inputs

Local ring:
  m contains zero and is closed under addition and scaling;
  dec decides for each a either m(a) or that a is a unit;
  rad gives that 1-a is a unit when m(a).

Prime:
  q has the ideal laws, contains the image of m, is proper, has the
  constructive prime disjunction, and membership in q is decidable.

Local ZMT data (exactly the previous TheoremLocal interface):
  an R-algebra B and map j : B -> E;
  a nonempty finite list spanning B over R, with mere coordinates;
  s in B with j(s)-1 merely in mE;
  for every z in E, merely k,b with j(s)^k z = j(b).
  This is the finite-algebra and denominator-clearing data used by
  the proof.  An injectivity hypothesis on j is not needed.

FieldData (as in etale-local/TheoremLocal):
  finitely many eps_i,x_i in B, with sum eps_i = 1 modulo mE after
  multiplying by a power of j(s); for each i, a coefficient list P_i
  and root, separability and generation witnesses, multiplied by
  eps_i and suitable powers of s.  Full signatures are PRoot,
  PSeparable, PGenerates, Piece and FieldData in FlatTheoremLocal.seg.
  PGenerates is a witness-producing function, as in the existing API.

The shared residue-field theorem is assumed at this exact interface.
Converting a differently stated field decomposition into these lifted
witnesses is not included.  The field theorem itself, its base-change
interface for formal unramifiedness, and primitive-element results
are not proved here.  See ../etale-local/FIELD-CASE.md.

5. Construction of the transfer theorem

The proof constructs the scalar extension explicitly as

    D = (T[X]/q_T)[1/(g q')_T].

Finite simultaneous coefficient relations prove flatness of D over
the explicit chart for S.  This uses polynomial flat base change,
principal quotient base change, and localisation.  FlatStandardChart
identifies this chart with the given universal-property S.

There are maps left:S->D, right:T->D, mu:D->T with mu right = id.
Let a=left(x), b=right(u(x)).  Both are roots of q, and q'(a) is a
unit.  Synthetic division q(X)=(X-a)H(X) gives

    e = H(b)/H(a),     e a = e b,     mu(e) = 1.

Passing to D/Ann(e) and using S's universal property extends this
equality from x to every s in S.  Thus t |-> e right(t) is an
S-linear section of mu.  The module retract of flat D is flat T.
The proof does not require e to be idempotent.

For the flat-kernel theorem, explain the relation x*1=0 in T by
flatness: 1 = sum u(c_j)t_j, with x c_j=0.  Lift the finite family
t_j under truncation, put z=sum c_j lift(t_j), and b=1-z.  Then
u(b)=0 and x=x b.  Finite choice occurs only inside truncation.

For square-zero lifting, lift a root modulo N to a representative a,
lift the inverse of q'(a), and put b=a-q(a)/q'(a).  Taylor's identity
and N^2=0 give q(b)=0.  The inverted polynomial remains a unit.
StandardEtale's existing uniqueness theorem makes the type of a
lift with its reduction equation a proposition, so the mere choices
of representatives produce an actual unique lift without choice.

6. File organisation

Finite-equation flat base change:
  FlatSystems, FlatFiniteSums, FlatPolynomialData,
  FlatPolynomialExpansion, FlatPolynomialRelations,
  FlatPolynomialBaseChange, FlatPrincipalBaseChange,
  FlatPrincipalQuotient, FlatLocalizedSource, FlatPowerLocalization.
Charts and the retraction:
  FlatPolynomialChart, FlatStandardChart, FlatRootFactor,
  FlatEvaluationBaseChange, FlatSeparabilityElement, FlatSourceIso,
  FlatRetraction, FlatAnnihilatorComparison, FlatSeparableRetraction,
  FlatStandardTransfer.
Kernel and local theorem:
  FlatQuotient, FlatStandardQuotient, FlatBaseStandardQuotient,
  FlatPresentedLocalization, StandardEtaleLift, FlatLocalStatement,
  FlatLocal, FlatTheoremLocal, FlatRegression.

FlatLocal and FlatTheoremLocal adapt the existing candidate and
factor-selection code.  Their inputs replace Etale E by finite
presentation and flatness; the ending is replaced by the new proved
flatness argument.  The original files remain unchanged.  The
candidate code was copied because the original modules bundle the
lifting hypothesis into their parameters; the algebraic construction
before the ending is the same.

7. Validation

Fresh built checker, All.seg --opened:
  7076 declarations, 0 failed, 2.80 s;
  1345 new declarations in 29 new proof modules;
  every new declaration <= 0.04 s, at most 29 distinct definitions
  opened (including module applications and their parameter checks).
./segc sag/etale-flat-unramified all:
  162 modules, 0 failed, 2.37 s.
Baseline sag/etale-local/All.seg:
  3985 declarations, 0 failed, 1.51 s.

etale-flat-unramified.opens records the expected openings for 93
central declarations, including applications and parameters.  The
fresh --opens run reports "nothing else opened" for all 93, with
7076 declarations, 0 failed, 2.65 s.
The
lists explicitly include quotient carriers and operation aliases:
the implementation opens some concrete quotient definitions as well
as the mathematical names.  This is a partial conversion audit;
the fresh All.seg check checks every proof, not only those listed.

FlatRegression constructs the standard source for X^2-X over Z/4Z
and the evaluation map x |-> 0.  The transfer theorem gives target
flatness over that source, and FlatQuotient is applied to x.
Evaluation at one proves x is nonzero.  The source also receives the
new Etale proof.  All polynomial representatives are chosen inside
truncation.  This is a regression of the new ending, not a complete
concrete instantiation of the local candidate construction.

Two intentional mutations were rejected, then restored and rechecked:
  - replacing 1-z by 1+z in the kernel witness;
  - using the positive Newton correction instead of its negative.

Commands from unit/:
  ./segc sag/etale-flat-unramified all
  SEG=$(cabal list-bin exe:seg)
  "$SEG" sag/etale-flat-unramified/All.seg --opened
  "$SEG" sag/etale-flat-unramified/All.seg \
    --opens sag/etale-flat-unramified/etale-flat-unramified.opens
  ./segc sag/etale-flat-unramified stop

8. Remaining work

Supply the explicit local ZMT and residue-field inputs from the
chosen upstream results.  The present local theorem does not depend
on a global ZMT theorem, but it does require local ZMT data.

For the arbitrary-base statement: the dynamical local-global finite
cover construction, and assembly of local square-zero lifting into
global lifting, remain separate work.  No such cover or global
flat-plus-unramified theorem is claimed here.
