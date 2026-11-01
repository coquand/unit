Constructive local--global passage by finite radical/unit trees
===============================================================

1. What is finished, and what is not

The constructive finite-tree-to-cover theorem is checked, including
actual algebra-valued chart certificates. The monic first-unit scan
used in the local idempotent argument is also constructed as a finite
tree, rather than taking a decision function on the coefficient ring.
Its leaves give the relation, idempotent and annihilation statement.
Standardness after localisation at F(x) is proved at the level of the
full algebra universal property, and complementary monic standard
charts are actually constructed.

This does NOT finish the full global etale structure theorem from its
original hypotheses. Replaying the remaining local proof, assembling
its original inputs, and descending the leaf charts are still required.
An arbitrary primewise existence theorem has not been transformed into
a finite tree. No proof interpreter or general conservation theorem is
claimed.

2. The generic constructive cover theorem

  DynamicalCertifiedCover.Over[A,setA,Certificate].theorem

Certificate : A.R -> U(l+) may contain actual algebras, maps and their
universal properties. A state is a pair of finite lists (I;U), with
denominator set S(I;U) = M(U) + (I). The radical branch adjoins a to I;
the unit branch adjoins a to U. Both branches are retained.

The input is Proof.Cover T.root: merely a finite tree, each leaf carrying

  s : A.R;
  an explicit membership witness s in S(I;U);
  Certificate s.

The conclusion is merely Cover, consisting of

  n : Nat;
  s,a : Fin n -> A.R;
  (i : Fin n) -> Certificate (s i);
  sum_i (s i)*(a i) = 1.

The proof forgets only the large certificate, applies the existing
FormalMonoidCover partition theorem to the small denominator choices,
and retains each certificate by recursion on the same finite tree.
No proposition resizing or infinite choice is used. The finite trees
have a leaf constructor and a binary branch constructor; there is no
infinite-tree compactness premise.

LargeTreeCover provides immediate, join, Map and Bind for large leaf
data, and FromSmall for continuing existing small tree procedures into
large certificate constructions. Mixed universes are handled with
explicit small Fin indices and identity elimination.

3. Exact chart interfaces

  DynamicalEtaleCover.Over[A,setA,E,setE,iota].theorem

uses the actual Local.Statement localisation universal property. Its
Chart s consists of an A-algebra T, an algebra map E -> T, the property
T = E[1/s], polynomials Q,G, and StandardEtale.Points[Q,G].Standard T.
The input is a tree of denominators and such charts over the ORIGINAL
base A. It is not a theorem taking only local data over A_p.

flat-theorem additionally retains FormallyEtale.Etale for each chart.
It does not assemble a global FormallyEtale.Etale proof for E.
monic-theorem retains a coefficient list followed by the leading 1.
The old Local.Statement does not record monicity, so the monic endpoint
has its own stronger input, with forget-monic to the old chart type.

4. A constructed part of the local proof

  DynamicalCoefficientScan.Over[A,setA].scan cs state

For cs = [c_0,...,c_(d-1)], this scans the monic list cs followed by 1.
The coefficients here belong to the original ring A. It tests c_0,
continuing along the radical branch and stopping on the unit branch.
The final leading 1 terminates without a further test. At each leaf:

  - there is an actual ring map from the initial node ring to that leaf;
  - the map commutes with A and preserves the radical ideal;
  - all coefficients before the selected one lie in the leaf radical;
  - the selected coefficient is a unit in the leaf ring.

All node rings and maps come from the checked monoid localisations;
these are not postulated records. No units of A are decided.

FirstUnitRelation removes the global dec parameter of IdempotentModM
and reads a finite First certificate instead. Its normalization, shift,
idempotent and annihilation proofs are the decision-free algebraic
bodies extracted from etale-local/IdempotentModM; the shared original
is untouched. Interpret in DynamicalCoefficientScan applies this to
ANY algebra B over the leaf ring, an ideal J containing the image of
the radical ideal, and a root s of the mapped monic list modulo J.
It gives, explicitly:

  s^k(1-sv) in J;
  N = k+1, e=(sv)^N;
  e^2-e in J, s^N(1-e) in J, e=s*cofactor;
  s^K*w in J implies e*w in J.

DynamicalScanCover.Given[finish].theorem composes the actual scan with
a leaf continuation. Only finish is a parameter; it must produce a
finite certified subtree at each scan leaf. The full etale continuation
has not been supplied.

5. Actual standard localisation and a two-chart application

  StandardChartLocalisation.Over[A,setA,E,Q,G,st,F0]
    .Given[T,i,localisation].standard

If E is standard for (Q,G), T = E[1/F0(x)] is standard for (Q,G*F0),
with the same Q. The proof constructs the inverse to the point map and
checks both inverse identities. It uses StandardEtale.Localise's point
calculation but proves the full algebra universal property.

Presented[p,pa,expression,rep] constructs T and its localisation property
using the existing Localization construction. Nothing asserts existence
of the localisation without constructing it.

  DynamicalStandardCover.Over[A,setA,E,lower,G,st,p,pa,F0].theorem

constructs a finite monic standard cover from the two localisations at
F0(x) and 1-F0(x). Here E is already a presented monic standard algebra;
this is a substantive example of the mechanism, not a proof that an
arbitrary etale algebra is standard. The two charts use G*F0 and
G*(1-F0). Representatives in the finite presentation are selected only
inside the final truncation. DynamicalComplementaryCover builds the
actual radical/unit tree and its denominator membership witnesses.

6. What remains for the original global theorem

- Supply the remaining original inputs of the existing local theorem:
  localised fibres, compatible primes/relations and ZMT outputs, wherever
  the current local integration still takes them explicitly.
- Replace the other local decisions, including factor selection and
  field-theoretic steps as required, by compatible finite branch
  procedures. The coefficient scan proves one real part of this job.
- Transport the base/algebra diagrams through those branch maps.
  The current scan uses coefficients from the original ring; a scan
  starting with fractional coefficients needs finite representatives
  and denominator transport, as in the earlier FiniteCoefficientTest.
- Descend each final chart, its equations and inverse-map certificates
  to one denominator in the leaf's S(I;U). A chart over the node ring
  alone does not constitute a leaf of DynamicalEtaleCover.
- Complete the separate finite-character/base-localisation descent and
  monic rescaling from the localised base to the original base.
- Compose the constructed tree with the already checked cover theorem.

ClassicalEtaleCover and DynamicalEtaleCover consume different inputs.
The former consumes primewise neighbourhoods and uses its explicit
classical parameters. The latter consumes finite branching evidence
and uses no classical parameters. Neither adapter by itself supplies
the remaining local integration and descent.

7. Validation (31 October 2026)

Fresh All.seg --opened: 5789 declarations, 0 failed, 1.95 s.
There are 367 new named declarations in eleven proof modules.
segc all: 154 modules, 0 failed, 1.71 s.
Fresh --opens: 5789 declarations, 0 failed, 2.26 s.
The unchanged etale-local baseline: 3985 declarations, 0 failed, 1.39 s.
All 367 new named declarations are covered by the .opens inventory;
each reports "nothing else opened". This is an observed dependency
inventory, not an independently specified informal proof budget.
Each new declaration reports 0.00 s at two-decimal precision and opens
at most 19 distinct definitions.

DynamicalRegression checks:
- a and 1-a, large certificates, and the two ordered leaf values;
- constant, linear and quadratic monic scans over every base ring;
- continuation of an actual small scan into a large certificate;
- the first-unit relation for [0,1], including its computed skipped
  coefficient count, idempotent, divisibility and annihilation;
- the constant monic relation in the zero ring, with skipped count 0;
- actual StandardAlgebra.Build for Q=X, G=1 over every ring, followed
  by construction of complementary monic standard charts.

Four deliberate mutations, in isolated temporary copies, were rejected:
- replacing sum_i s_i*a_i = 1 by = 0;
- replacing the monic leading 1 by 0;
- using the inverse branch in place of the radical branch;
- replacing G*F by G+F in the standard localisation.
The working sources were never mutated.

The development uses only the existing univalence, replacement and
surjection parameters of All.seg. No new axioms, no excluded middle,
no prime-existence principle, no choice or resizing axiom. All reused
sources are relative links. No shared formal source or checker source
was changed. Nothing is committed.
The checking server is stopped.

8. Commands and mathematical account

From unit/:

  ./segc sag/etale-dynamical-global all
  ./segc sag/etale-dynamical-global stop

Fresh checker:

  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-dynamical-global/All.seg --opens \
    sag/etale-dynamical-global/etale-dynamical-global.opens

doc/etale-dynamical-global.tex (and PDF): mathematics first, then the
connection with Unit and the exact remaining obligations.
doc/etale-local-proof.tex is updated to distinguish the checked bridge
from the unfinished construction of the complete etale proof tree.
