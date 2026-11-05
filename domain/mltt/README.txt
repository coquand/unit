domain/mltt: MLTT_eta (Pi, U : U, beta, eta) after Carneiro, Coquand,
Frabetti Mathieu, Lennon-Bertrand, Mellies, Weirich, "Definitional
inversion, without normalisation" (~/DOMAIN/paper1.pdf, arXiv 2607.13662),
section 2; a port of ~/DOMAIN/MIN (its Agda mechanisation, 27k lines) with
the compact elements as INTERSECTION TYPES (user's choice, 2026-11-05).
Not committed.

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

NEXT
 4. Logical relation by recursion on the depth of the witness (Nat),
    Pi clauses per entry, Unit records for the clauses; its laws
    (sec. 2.7); adequacy (Thm 2.35); Pi injectivity, subject reduction.
 Confluence (MIN/Syntax/Confluence*) is not needed.

CHECK.  From here: $(cd ../.. && cabal list-bin exe:seg) All.seg
