domain/mltt: MLTT_eta (Pi, U : U, beta, eta) after Carneiro, Coquand,
Frabetti Mathieu, Lennon-Bertrand, Mellies, Weirich, "Definitional
inversion, without normalisation" (~/DOMAIN/paper1.pdf, arXiv 2607.13662),
section 2; a port of ~/DOMAIN/MIN (its Agda mechanisation) with
the compact elements as INTERSECTION TYPES (user's choice, 2026-11-05).

DONE.  Types.seg (152 declarations with Lib, 0 failed, 0.02 s; no
parameters): types om | univ | pi s t | arr s t | meet s t; order Le by
inference rules (pi covariant in both arguments; om <= om -> om, the
coalesced sum lambda(bot) = bot, which validates eta); syntax-directed Les
and transitivity by depth induction on Nat (depth-0 middle with an empty
arrow selection settled by omonly-les); inversion inv-univ, inv-pi,
inv-arr (beta-soundness); no confusion om-not-univ, om-not-pi,
univ-not-pi, pi-not-univ.  Replaces MIN's Domain/Order* and Rank*.

DONE (steps 1, 2; informal argument NOTE-1-2.txt, written first).
All.seg: 285 declarations with Lib, 0 failed, 0.03 s; no parameters,
no postulates; --opened at most 5 per declaration, all named by the text.
 Consistency.seg (59 decls): clauses CL P r (no U/Pi clash; U or Pi with
    an arrow selection of consistent domain => om-like codomain; pi
    selections consistent; arrow selections: consistent domain =>
    consistent codomain).  C N by recursion on fuel N, Cons r = C (md r) r;
    c-move (enough fuel: Lemma 1.1), cons-fix (Cons r <=> CL Cons r), then
    `opaque Cons`; cons-down (r <= k, Cons r => Cons k), cons-pi, pi-inj.
 Typing.seg (74 decls): ONE family Tp over data Form = el u a | ent f A phi
    (ent = "entries of f typed over A, phi": x : A, phi <= x -> y, v : y).
    Rules Bot, Univ, Pi, Lam conclude u : a for any u, a == canonical form,
    so no conversion rule; Pi's family is ent phi A (om -> U) + Cons phi;
    Lam's representation f is existential (u == f) + Cons f.  Proved:
    tp-conv, tp-pre, shape (generation) + below-univ/below-pi/pi-dom,
    tp-cons (typed => consistent), tp-up (paper 2.17; needs a' : U),
    tp-join (paper 2.16, with Cons (u /\ v)), ent-sel and app-sel (values
    of a typed function at a selection of entries are BELOW a typed element
    of phi(x): typing is not downward closed in the element).
 Paper 2.15 is the definition here (intensional form, as in the paper's
 three formalisations); app-sel is what is used of its extensional form.
 Stability (2.18) has no counterpart (no stages).

DONE (step 3; informal argument NOTE-3.txt, written first).
All.seg: 576 declarations with Lib, 0 failed, 0.08 s; no parameters, no
postulates.  sem is locked (opaque) at the end of Sem.seg; from there on
it is used through its clause equations sem-var-eq .. sem-app-eq (FEq)
and the lemmas of Sem.seg.  Check with --opened after the file name.
 Syntax.seg: Fin n by recursion (Fin (n+1) = Opt (Fin n)); Tm n an indexed
    family; record Kit + module Trav (one traversal), instances renK (wk)
    and subK (subst1); Ctx n by recursion, lookup; the judgements as ONE
    family Der n J over Jf n = jwf G | jty G M A | jeq G M N A (MIN's rules).
 Filter.seg: record Filt (not truncated), Incl/FEq, prin, univF; EntS R f
    (entries); TyIn A x (x : a for some a in A); appF, lamF, piF, each a
    filter for EVERY argument (each entry carries its own domain witness);
    Entries.sel (Lemma 3.1), Entries.cons (3.2), ents-in (3.3).
 Sem.seg: environments of filters (paper's EnvD); sem by recursion on Tm;
    sem-mono (3.4), sem-cons (3.5), cont / cont-last (3.6 continuity, used
    only by beta), SemTrav over a kit (3.7) with instances wk-sem and
    subst1-sem (paper 2.29).
 Sound.seg: Enl / HasTy (A : B iff every element of A is BELOW a typed
    element of A), Fits (2.30), Lemmas 3.8, 3.9; per rule a lemma on the
    filter operations (sound-pi, sound-lam, App, Beta, Eta); sound = one
    eliminator on Der; Theorem 2.31 soundness-ty, soundness-eq; Theorem
    2.32 for the empty context (pi-not-u-closed).
 Typing.seg change: app-sel (Lemma 2.8) now also gives f <= x -> w.

DONE (step 4a; informal argument NOTE-4.txt 4.1-4.5, written first).
 SynLemmas.seg  equations on terms over the kit (E0-E4, D1-D4)
 Weaken.seg     Lemma R (renaming of derivations), weakening
 Subst.seg      P0, Lemma S (substitution), sub1, identity, context conversion
 Presup.seg     wf inversion, lookup : U, type and conversion presupposition
 Cross.seg      Lemma X: two equal substitutions give equal instances
STEP 4b, PARTLY (NOTE-4.txt 4.6-4.12).
 Reduction.seg  head reduction as a function (deterministic by construction)
 LogRel.seg     Dom/Cod/Fam of a filter, Lemma 4.7.1, the relation at
                FILTER witnesses by fuel, laws L0, L1, L7, L8
 Laws.seg       L2-L6 (diagonal, symmetry, conversion, transitivity)
All.seg: 853 declarations, 0 failed, 0.14 s, no parameters, no postulates.
DONE (step 4b at compact witnesses; NOTE-4.txt 4.14, written first).
4.12 (adequacy fails at a fixed fuel) is settled by 4.14 (decision 4.13):
compact witnesses, the arguments read off the arrow selections of the
ELEMENT witness (as MIN), no type witness; stability is the enough-fuel
Lemma F.  LogRel.seg / Laws.seg stay as the record of 4.8.
 RelC.seg         the relation (4.14.1), M (monotone in the witness), L1,
                  Lemma F, TyR / TmR at the canonical fuel, unfolding
 LawsC.seg        L2-L7 at every fuel; L3-L6 with a typing hypothesis,
                  through the typed representative (key-tp, fam-val)
 AdeqBase.seg     the substitution (s, P); the laws at the canonical
                  fuel; related substitutions (both types), sym, diag, ext
 AdeqPi.seg       statement Ad; var, conv, U, Pi / eq-Pi
 AdeqLam.seg      refl, sym, trans, lam
 AdeqApp.seg      app / app-fun / app-arg, beta
 AdeqFun.seg      funext
 Adequacy.seg     Theorem 2.35, one eliminator on the derivations
 Consequences.seg bottom environment, identity related, Corollary 2.37
                  (pi-injectivity) in any context
All.seg: 1486 declarations, 0 failed, 0.25 s; no parameters, no
postulates.
DONE (subject reduction, paper 2.38; NOTE-4.txt 4.15, written first).
 SubjRed.seg      gen-lam (generation for lam up to conversion, motive by
                  cases on the subject), beta-ty (pi-injectivity, Lemma S),
                  subject-reduction (one eliminator; app by cases on the
                  function), subject-reds (along ~>*)
All.seg: 1507 declarations, 0 failed, 0.26 s; no parameters, no
postulates.

COMPARISON WITH THE AGDA DEVELOPMENT (~/DOMAIN/MIN), same machine.
 Agda 2.9.0, no interface files, MIN/SubjectReduction.agda and all it
 imports: 54 modules, 21,987 lines, 1.10 MB, 13.0 s (0.30 s on cached
 interfaces).  Unit: 27 files, 6,045 lines, 0.34 MB (library included,
 LogRel/Laws excluded), All.seg 0.26 s.  By part (characters, Agda / Unit):
 domain 231k / 56k, syntax 55k / 78k, model 224k / 67k, relation 219k /
 46k, adequacy 361k / 66k, Pi injectivity + subject reduction 14k / 12k.
 See the top-level README.md for where the difference comes from.

CHECK.  From here: $(cd ../.. && cabal list-bin exe:seg) All.seg
