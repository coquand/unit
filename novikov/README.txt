Novikov's consistency proof (P. S. Novikoff, "On the consistency of certain
logical calculus", Mat. Sbornik 12 (54), 1943, 231-261) in Unit.

The rule of inference is admissible for regular formulas, by induction on
regularity proofs and without induction on the cut formula.  Two proofs:
Novikov's, with his operators B_tau and A_tau (sections 7-8,
Operators.seg), and the variant of the appendix of Coquand, "A semantics
of evidence for classical arithmetic" (Variant.seg), which keeps Novikov's
definition of regularity and replaces the operators by a direct
cut-elimination argument.  Neither uses induction on the cut formula.
Consequences: the consistency of the infinitary calculus, PA induction as
a regular formula, the auxiliary theorem of section 10 (announced in the
note of 1939, "Sur quelques theoremes d'existence", C. R. Acad. Sci. URSS
23, 438-440): a regular sum of finitary formulas has a regular finite
part, with the bound computed from the proof; and Novikov's application
built on it (section 10): from a proof of exists n F(n), F decidable, one
computes n with F(n) true (Markov's rule).  The formulas are built from Novikov's letters A_n (no fixed truth
value) and constants x_n, whose truth values are the parameter
val : Nat -> Bool of the development (All.seg).  No new
axioms; the only parameter is val.

Check:  (cd novikov && "$(cabal list-bin exe:seg)" All.seg)
        379 declarations, 0 failed, 0.06 s;  or  ./segc novikov all
        (needs a checker with indexed inductive families, main >= 03bd5bc5)

Files
  Base, Paths  small types; symmetry and transport for Id; Or.
  Formula      formulas  F0 | F1 | X n | NX n | L n | NL n | Sp (f : Nat -> T)
               (0, 1, the constants x_n, ~x_n, the letters A_n, ~A_n,
               normal forms of s. 6); Fm, finitary formulas over letters
               and constants;
               negation, the summands comp a k, sequents (Nat -> T), cons,
               W u (a product entering a sequent), NegS G (negation of a
               sequent).
  Regular      regularity (s. 4): the inductive family Reg, with
               constructors ax (the distinguished term is 1 or a true
               constant), lax (the axiom A v ~A on a letter) and pi (the
               distinguished term is a product, with the constituents);
               focus (the rule), regInd (its eliminator), notEmpty;
               inclusion Sub G H and weak (s. 5: Lemmas 1, 3, 7, and 14:
               removal of 0 and of false constants); Replace, the induction scheme of the lemmas.
  Identity     F v ~F is regular (s. 8), the only induction on formulas in the
               proof of the cut rule;
               inv: a factor can replace a product (Lemma 1).
  Cut          shared by the two proofs: Elim (eliminability), AndSum (the
               opening of brackets, Novikov's Lemmas 9-12 = Lemma 5 of
               the appendix), AtomCut (the atomic cut, Lemma 13),
               letterLeaf, cutBy (the cut rule from eliminability).
  Operators    Novikov's proof: B_p (the product of the leaves of a
               regularity proof p, which is Novikov's tau) and A_p = neg B_p
               by recursion on p; Lemma 17 (Open17), Lemma 18 (lemma18:
               W (neg D) , B  regular => A_p , B  regular), Lemma 15
               (lemma15: A_p , B regular => B regular); elim, cut, mp
               (rule 5), consistent.
  Variant      the appendix: SumElim (Lemma 6), elimV (Proposition 2),
               cutV.
  Calculus     the inductive family Provable (ax, pi and cut); regular
               (with Novikov's cut) and regularV: every provable sequent is
               regular (the principal theorem, s. 8); consistency.
  Arithmetic   Induction.induction (s. 9).
  Existence    s. 10: Witness (the last focus of a proof of a sum of
               constants is a true one); Holds/Fails/dec for finitary
               formulas; truth (Lemma A: true => regular, false =>
               negation regular, formulas without letters);
               Markov.markov and Markov.markovProof: Novikov's theorem, by
               his y_n = x or ~x and one cut.
  Finite       the auxiliary theorem of section 10 (announced in 1939): hereditarily finite formulas (HF),
               finite parts SN N of a sum, Bound.bound (a regular sum of
               HF formulas has a regular finite part, by induction on
               regularity, no cut), auxTheorem and auxTheoremProof for
               finitary formulas.
  Examples     val = even, F(n) = ~x_n & x_(n+1); the sum proved by F(3);
               the witness computed through either cut elimination is 3;
               likewise for a proof with a cut on the sum itself (left
               premise by F(5), right premise by F(3)); the theorem of 1939
               through a cut on the letter A_0 (G(6) = ~A_0, G(7) = A_0):
               both eliminations give N = 7.

The definition (Regular.seg).  A sequent G (a sum) is regular if, for some
summand c = comp (G m) k (a product):  c is 1 or a true constant;  or
c = Sp g and every  g j , G  is regular.

Novikov's proof (Operators.seg).  D is eliminable if B is regular whenever
W (neg D) , B is.  For a regularity proof p of D:
  B_p(D)    the product of the leaves of p;  A_p = neg B_p(D)  (Novikov's
            duality A_tau(~F) = ~B_tau(F) holds by definition).
  Lemma 18. W (neg D) , B  regular  =>  A_p , B  regular.  Induction on p:
            two inversions, the opening of brackets (Cut.AndSum), and
            Lemma 17 (apply A_(p_j) inside each summand).
  Lemma 15. A_p , B  regular  =>  B  regular.  Induction on p: the leaves
            of A_p contain the negation of a true atom, a false atom.
  So every regular sequent is eliminable (elim), and the cut rule follows
  (A , G  and  W (neg A) , G  regular  =>  G regular,  since
  W (neg (A , G)) , G  is regular by identity).

The variant (Variant.seg).
  Lemma 5.  W (neg D) , B  and  Sp (neg o e) , B  regular  =>
            Sp (\ j -> neg (e j , D)) , B  regular.
  Lemma 6.  every D j eliminable,  Sp (\ j -> neg (D j)) , B  regular  =>
            B regular.
  Prop. 2.  D regular => D eliminable.  Induction on the proof of D, last
            focus on c = comp (D r) k; inner induction on the proof of
            W (neg D) , B: at a focus on neg D, the r-th premise and
            inversion give  neg c , B;  for c true remove neg c; for
            c = Sp g the premises  g j , D  are eliminable (outer
            induction hypothesis), and Lemmas 5 and 6 give B.
  Cut.      A , G  and  W (neg A) , G  regular  =>  G regular  (Prop. 2
            for D = A , G, with  W (neg D) , G  regular by identity).

Differences from Novikov's text
  - Letters and constants (with the empty sum 0 and product 1), but no
    substitution rule 4: the calculus with cut has the three rules of
    regularity and the cut rule.
  - The distinguished term is kept in the premises (Tait), not removed
    (i /= r).  By weakening, the regular formulas are the same.
  - Sums are merged by putting the formulas side by side in a sequent,
    which takes the place of the operation ~ of section 3.
  - Two proofs of the rule of inference.  Cut.seg follows Coquand's
    appendix.  Operators.seg follows Novikov: tau is the regularity proof
    itself, and the duality A_tau(~F) = ~B_tau(F) holds by definition.
    His Lemma 15 is by induction on p and on regularity, since the
    summands of A_p are nested along p; the pairs A ~A are removed by
    atomic cuts (Lemma 13).  Neither proof uses induction on formulas.
  - The calculus is a sequent calculus with cut, not Novikov's axioms 1-3
    and rules 4-6.  Axiom 3 and rule 6 are foci, and rule 5 is mp.  The
    finitary tautologies (axiom 2) are not formalised.
