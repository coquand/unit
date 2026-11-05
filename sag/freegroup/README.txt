The free group on a set, as a filtered colimit of free groups on finite
sets, with the size results of group1.pdf ("Size and free structures") for
groups.

Theory parameters: univalence and replacement (images, surjections), as in
sag/; function extensionality, truncation and set quotients are derived
(FunExtUA, Truncation, Quotient: symlinks).  No new axioms, no HITs.

Idea.  On a type with decidable equality the free group is the group of
reduced words (decidable).  A set X is the filtered colimit of the stages
(c, f : El c -> X), c a code for a finite type (0, 1, +); F(X) is the
colimit of the free groups on the stages: an element is a stage with a
reduced word over it, and (s,u) ~ (s',v) iff some stage t has maps m, n
from s, s' over X with m u = n v.  Transitivity uses the coequaliser lemma:
two maps into a stage are made equal by a further map (merge the pairs one
at a time).

The colimit half is generic: it uses only the interface FinFree (Interface)
of free structures on the finite stages.  Two instances: free groups by
reduced words (FreeInstance, all target groups) and free abelian groups
Z^c (AbelianInstance, abelian target groups).

Files
  Decisions   Booleans as decisions; discrete types (record Discrete)
  Codes       codes FT for finite types, El, decidable equality, decide
  Words       Free[D]: reduced words, act/ev (van der Waerden), group laws,
              gen-inj, Occ
  Group       record Grp, idem, inv-unique, HomL
  Functor     Map[D,E,s].fmap = F s; Comp, Ident, Ext; occ-fmap
  Universal   UP[D,G,f]: lift, lift-mul, lift-gen, Unique; Natural
  Stages      stages, maps of stages, sums, Merge.coequalise
  Interface   record FinFree (what the colimit uses)
  FreeInstance  free : FinFree (groups)
  Colimit     Colimit[I,X]: Elt, Link, Trans, the quotient, laws up to links
  FreeGroup   FreeGroup[I,X]: mul, inv, one, laws, FX : Grp, eta
  Lift        Lift[I,X,G,tG,f]: lift, lift-mul, lift-eta, Unique.unique
  Injective   Injective[I,X,setX].eta-inj
  FinSum      Sums[A]: finite sums in an abelian group, Fubini, delta rule
  Multiples   Mult[A]: integer multiples, mult-add, mult-sum, FromZ
  AbelianInstance  abelian : FinFree (Z^c, push = sums over fibres)
  SmallProp   SmallProp[B].prop : isProp (Small B) (univalence)
  Identification  Ident[I,X]: [x] = [y] iff merely one identification r
              of the formal variables with g o r = g and (r inl) u = (r inr) v
  Small       Size[I,E,setE,ls]: small-eq, small-fib at representatives;
              locally-small, small-fibres at every element
  Abelian     AbelianFree[X].comm: the abelian colimit is commutative
  AbelianEquality  AbEq[X]: equality in A(X) by (1) an identification with
              equal fibre sums, (2) a partition with equal class totals,
              (3) a finite disjunction over the codes of maps El c -> El c
  AbelianExamples  Ex[E,setE,e0,e1,e2]: e0-e1+2e2 = e0+e1 iff e1 = e2; the
              fibre of eta at e0-e1+e2 is ||e0=e1 or e1=e2||; at e0-e1+2e2 empty
  Theorems    the statements for both instances (free-*, ab-*)
  linked: Base Prelude Paths Axioms FunExtUA (core), Replacement Truncation
  (replacement), Quotient (projective), EquivProp (em), NatArith Logic
  Torsor Integers (stoneseq)

Main statements (Theorems.seg)
  free-group X, free-lift-mul, free-lift-eta, free-lift-unique
      the free group on any X : U k and its universal property
  free-eta-inj            eta injective for a set X
  free-locally-small, free-small-fibres
      group1.pdf: E a locally small set => F(E) locally small, eta has small
      fibres (at every element)
  ab-group X, ab-comm, ab-lift-mul, ab-lift-eta, ab-lift-unique,
  ab-eta-inj, ab-locally-small, ab-small-fibres
      the same for the free abelian group A(X)
  ab-eq-identification, ab-eq-partition, ab-eq-finite
      equality in A(X): the three forms
  ab-example1, ab-example2, ab-example3   the three examples

Levels: the finite stages live in U l, the generators X in U k (l <= k), so
that for E in U l+ locally small the words over a stage stay in U l.

Check (from unit/):   ./segc sag/freegroup all
  2026-11-05: 37 modules, 0 failed, 0.22 s (1255 declarations).
