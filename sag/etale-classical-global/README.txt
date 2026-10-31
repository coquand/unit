Classical passage from primewise neighbourhoods to a finite cover
================================================================

1. Scope and classical boundary

This is a checked classical local-to-global segment. It proves that
primewise certified principal neighbourhoods give a finite certified
principal cover, with an explicit equation sum_i s_i a_i = 1.

It is conditional on two explicit parameters, both confined to
  Theory.Classical.Cl[lem,prime-existence]:

  lem : excluded middle for propositions, at every universe level;

  prime-existence : for every commutative set-ring, every proper ideal
    with propositional membership is merely contained in a prime ideal.

PrimeExistence.seg, imported OUTSIDE Classical.Cl, defines the type of
the second principle. It does not assert an inhabitant. Its primes have
propositional membership, properness, and truncated disjunctive primality.
They do not come with a membership decision. ClassicalLogic constructs
that decision, and the exact existing PrimeIdempotents.Prime record,
using lem. A derivation of prime-existence from choice is left for later.

The existing univalence, replacement and surjection parameters remain
in Theory. No foundational or checker file is modified. The constructive
imports are outside Classical.Cl and acquire neither classical premise.
There is no global axiom asserting excluded middle or prime existence.

2. Generic finite-cover theorem

Inside Classical.Cl:

  ClassicalPrimeCover.Over[A,setA,G].Given[pointwise].theorem

G : A.R -> U l may carry witnesses and need not be proposition-valued.
The pointwise premise is

  for every prime q, merely (s, g : G s, outside : not(q s)).

The conclusion is merely Cover, where Cover contains

  n : Nat;
  s,a : Fin n -> A.R;
  good : (i : Fin n) -> G(s i);
  equation : sum_i (s i)*(a i) = 1.

The generated ideal is constructed using IdealGenerated: membership is
the truncation of a finite list of terms s*a with G(s). Its ideal laws
are proved. If 1 were not in this ideal, prime-existence would give a
prime containing it. Pointwise supplies a good element outside this
prime, while the ideal generator lemma puts it inside. Excluded middle
then gives 1 in the ideal, and its finite witness supplies the cover.

No simultaneous selection of one neighbourhood for every prime occurs.
The prime above the ideal and the pointwise witnesses are eliminated
only into propositions. The conclusion remains truncated.

3. Large certificates without a resizing axiom

  ClassicalCertifiedCover.Over[A,setA,Certificate]
    .Given[pointwise].theorem

allows Certificate : A.R -> U(l+), as needed for an actual algebra and
its universal property. ClassicalLogic.resize represents the proposition
|| Certificate s || by a small proposition, Top or Empty according to
excluded middle, with maps in both directions. The small predicates
generate the ideal. After the finite cover is found, constructive finite
choice restores all its actual certificates inside the final truncation.

No independent proposition-resizing axiom or axiom of choice is used.
ClassicalCertifiedCover.choice is the ordinary finite induction, with
small Fin indices and witnesses in the larger universe.

4. Exact etale interfaces

  ClassicalEtaleCover.Over[A,setA,E,setE,iota].Given[local].theorem

local takes every existing decidable PrimeIdempotents.Prime of E and
returns merely Local.Statement[A,setA,E,setE,iota,q.ideal.In].Conclusion.

The conclusion is merely Global.Cover. For each s_i it retains:
- an A-algebra T_i and an A-algebra map E -> T_i;
- the actual universal property T_i = E[1/s_i];
- polynomials Q_i,G_i and the existing StandardEtale.Points.Standard
  certificate for T_i;
- and, for the whole family, sum_i s_i*a_i = 1.

GivenFlat[local].theorem accepts the exact FlatLocalStatement conclusion
and additionally retains FormallyEtale.Etale for every chart. It does not
assert an assembled global FormallyEtale.Etale certificate for E.

Monicity is an explicit interface distinction. The older Local.Statement
conclusion quantifies Q but does not record that Q is monic. Consequently
Given does not manufacture a monicity proof. The stronger endpoint

  ClassicalEtaleCover.Over[A,setA,E,setE,iota]
    .GivenMonic[local].theorem

accepts primewise MonicChart certificates and returns MonicGlobal.Cover.
Each polynomial is explicitly a coefficient list followed by the leading
coefficient 1. This is the monic version in zmt2-revised.tex. A forgetful
map sends MonicChart to the older Chart interface.

5. What this does and does not finish

The compactness step is proved; it is not a new premise. The only
classical premises are lem and prime-existence. The etale application
still takes the primewise neighbourhood theorem over the ORIGINAL base.

To start instead with a theorem over A_p, the remaining integration must:
- construct the local setup at p = q intersect A and supply the local
  theorem's remaining original inputs;
- descend the finite presentation and isomorphism certificates to A[1/f];
- apply the monic rescaling/base-change lemma to return to A;
- retain monicity when exporting the stronger MonicChart conclusion.

Those steps are not supplied by excluded middle or prime existence and
are not claimed to have been formalised here. Neither full global etale
structure from its original hypotheses nor global flat + unramified =>
etale is claimed finished by this directory. The dynamical constructive
replacement for the classical segment is also outside this milestone.

6. Regressions and validation (31 October 2026)

ClassicalRegression checks:
- G(s) = (s=1), over every commutative set-ring;
- G empty in the zero ring, including the explicit empty cover;
- conversely, an empty-good cover forces 1=0 and is impossible in a
  nonzero ring;
- a,b with a+b=1, and in particular e and 1-e, without assuming either
  element is a unit;
- certificates containing a universe-valued component, exercising
  proposition resizing and finite restoration;
- an actual standard algebra constructed by StandardAlgebra.Build for
  Q=X, G=1, over every base ring. Its identity localisation at 1 is
  proved by the universal property. Both the ordinary and monic finite
  cover theorems are applied to it.

Fresh All.seg --opened: 4262 declarations, 0 failed, 1.49 s.
There are 217 new declarations in seven owned proof modules, plus All.seg.
segc all: 98 modules, 0 failed, 1.27 s.
Fresh --opens: 4262 declarations, 0 failed, 1.55 s.
The unchanged etale-local baseline: 3985 declarations, 0 failed, 1.37 s.
Every new named declaration is reported at 0.00 s (two-decimal timing),
and opens at most 11 definitions. The .opens file covers all 217 named
declarations in PrimeExistence and Classical, including parameters and
module instances. The full --opens audit reports nothing else opened
for each of them.

Three mutations in isolated temporary copies were rejected:
- replacing the unit-ideal equation by a sum equal to 0;
- applying prime properness to membership of the wrong element;
- replacing the leading monic coefficient 1 by 0 (caught by the actual
  constructed-standard regression).
The working sources were never mutated.

All reused sources are relative links. The checking server is stopped.
Nothing is committed.

7. Commands, from unit/

  ./segc sag/etale-classical-global all
  ./segc sag/etale-classical-global stop

Fresh checker:

  dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg \
    sag/etale-classical-global/All.seg --opens \
    sag/etale-classical-global/etale-classical-global.opens

The mathematical proof and the formal boundary are described separately
in doc/etale-classical-global.tex and the compiled PDF.
