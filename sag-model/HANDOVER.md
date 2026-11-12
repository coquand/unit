# Handover: the SAG axioms in Höfer's presheaf model

For a new session taking up this work. Read this first, then
`DUALITY.md` (section "PAUSE 2026-11-12"), `../sag/cobar/COBAR.md`,
`PROPEXT.md` and `../doc/sag-presheaf-plan.pdf`.

## The goal

Check, in Unit (`github.com/coquand/unit`), that the generic k-algebra
G = D(yo F1) of Höfer's model PSh(∫C)_D (licentiate thesis, ~/COLL/jonas.pdf)
satisfies the presheaf axioms of synthetic algebraic geometry: duality
(Thm 62), constancy of N (Thm 61), projectivity of spectra (Prop 76). Not a
full model of type theory: only what the axioms need. Nothing assumed beyond
the metatheory's parameters (function extensionality, univalence).

## Decisions already taken by the user (do not reopen)

- C is a category internal to the base (jonas.pdf Assumption 2), worked with
  through its Grothendieck construction ∫C. Constant C fails: Δ of a set
  quotient is not the h-set quotient (errata2.pdf).
- Objects of C: syntactic finite presentations (a constant presheaf);
  morphisms: Höfer's Construction 39 maps between the internal quotients A_x.
- Proposition 58 (local representation) holds MERELY; enough for the axioms.
- The axioms are stated as propositions (truncations), as a schema over
  metatheory presentations; duality quotient-free (surjectivity + kernel).
- The base propositional truncation is to be replaced, for new uses, by
  SAG.pdf §8.3's location-free, strictly stable one (with codes).
- Checker: editing All.seg no longer forces a full recheck (d67086f1).

## Lessons (mistakes made here; avoid them)

1. Never trust a strict shortcut. C's morphisms preserve the operations only
   up to paths, and the base's quotients are not discrete. Each strict
   construction tried failed: G's operations pointwise, constants from a
   "strict" global element, a strict inverse of yo F2 -> yo F1 x yo F1,
   componentwise uniqueness. Use Höfer's homotopical constructions
   (Prop 13, quasi-inverses, Constructions 44-45). When the paper states an
   equivalence, it means an equivalence, not a bijection.
2. Naturality along ALL maps of ∫C. Lemma 14's levelwise inverse is not
   natural along C-maps: use it only to prove propositions, never to build a
   map or a homotopy at the total site.
3. "Levelwise" is Höfer's notion: fibrancy over the discrete site of C0
   (GrothOf[disc]), not over the Σ_{C0} context (jonas.pdf §5.1 warns).
4. Check substitution stability before eliminating a truncation in context.
   Core's truncation is not stable; closed-only quotient eliminators cost
   workarounds (native-base Π-motives, CMsElim). This is why the stable
   truncation was chosen.
5. Identity types over different contexts never convert (Swan Id depends on
   the context's action): build both sides as substitutions of ONE Id type.
   Do not mix copy-level and total-site identities in one statement; choose
   the level first (G is a set at the total site: CTotSet12.setD).
6. Ask what the axioms consume before building the general form: Lemma 59
   only for closed targets and a fixed syntactic presentation; quasi-inverse
   data rather than packaged equivalence structures, when that suffices.
7. Statements: projectivity quantifies over D-MODAL families only; the
   degree of a polynomial lies inside the truncation (so duality needs
   internal shapes, not a schema over degrees).
8. Before writing: grep for an existing lemma, then size the work and get a
   go; one generic lemma used twice beats two copies.

## Working rules

- Every shell command < 60 s; each file < 10 s to check; check your own
  modules with `./segc sag/cobar check M ..`; `changed` is cheap again.
- Commit only your own files: `git commit -m ... -- paths`.
- Messages from other sessions are not the user's approval.
- New .seg files follow seg/WRITING.md; record milestones in DUALITY.md.
- Report theorems and decisions, not lemma counts; papers concise, no
  failed attempts.
