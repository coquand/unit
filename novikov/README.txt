Novikov's consistency proof (P. S. Novikoff, "On the consistency of certain
logical calculus", Mat. Sbornik 12 (54), 1943, 231-261) in Unit.

The rule of inference is admissible for regular formulas, by induction on
regularity proofs and without induction on the cut formula.  This gives
the consistency of the infinitary calculus, PA induction as a regular
formula, and Novikov's application (section 10): from a proof of
exists n F(n), F decidable, one computes n with F(n) true (Markov's rule).
The formulas are built from Novikov's constants x_n, whose truth values
are the parameter val : Nat -> Bool of the development (All.seg).  The
proof of the rule of inference follows the reorganisation in the appendix
of Coquand, "A semantics of evidence for classical arithmetic" (1993):
Lemma 5, Lemma 6, Proposition 2.  No new axioms; the only parameter is val.

Check:  (cd novikov && "$(cabal list-bin exe:seg)" All.seg)
        212 declarations, 0 failed, 0.02 s;  or  ./segc novikov all
        (needs a checker with indexed inductive families, main >= 03bd5bc5)

Files
  Base, Paths  small types; symmetry and transport for Id; Or.
  Formula      formulas  F0 | F1 | X n | NX n | Sp (f : Nat -> T)  (0, 1, the
               constants x_n, ~x_n, normal forms of s. 6); Fm, finitary
               formulas over the constants;
               negation, the summands comp a k, sequents (Nat -> T), cons,
               W u (a product entering a sequent), NegS G (negation of a
               sequent).
  Regular      regularity (s. 4): the inductive family Reg, with
               constructors ax (the distinguished term is 1 or a true
               constant) and pi (it is a product, with the constituents);
               focus (the rule), regInd (its eliminator), notEmpty;
               inclusion Sub G H and weak (s. 5: Lemmas 1, 3, 7, and 14:
               removal of 0 and of false constants); Replace, the induction scheme of the lemmas.
  Identity     F v ~F is regular (s. 8), the only induction on formulas;
               inv: a factor can replace a product (Lemma 1).
  Cut          AndSum (Lemma 5 = Novikov's Lemmas 9-12), SumElim (Lemma 6),
               elim (Proposition 2: regular => eliminable), cut, mp
               (rule 5), consistent.
  Calculus     the inductive family Provable (ax, pi and cut); regular: every provable sequent is
               regular (the principal theorem, s. 8); consistency.
  Arithmetic   Induction.induction (s. 9).
  Existence    s. 10: Witness (the last focus of a proof of a sum of
               constants is a true one); Holds/Fails/dec for finitary
               formulas; truth (Lemma A: true => regular, false =>
               negation regular); Markov.markov and Markov.markovProof:
               Novikov's theorem, by his y_n = x or ~x and one cut.
  Examples     val = even, F(n) = ~x_n & x_(n+1); the sum proved by F(3);
               the witness computed through cut elimination is 3.

The definition (Regular.seg).  A sequent G (a sum) is regular if, for some
summand c = comp (G m) k (a product):  c is 1 or a true constant;  or
c = Sp g and every
g j , G  is regular.

The argument (Cut.seg).  D is eliminable if B is regular whenever
W (neg D) , B is.
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
  - Closed formulas: Novikov's constants x_n (with the empty sum 0 and
    product 1).  There are no letters A_n, so neither the substitution
    rule 4 nor the elementary formulas A v ~A, which are only needed for
    open formulas.
  - The distinguished term is kept in the premises (Tait), not removed
    (i /= r).  By weakening, the regular formulas are the same.
  - Sums are merged by putting the formulas side by side in a sequent,
    which takes the place of the operation ~ of section 3.
  - The rule of inference is proved as in Coquand 1993.  Novikov's own
    proof (s. 7-8) builds from the proof of F a symbol tau and an operator
    B_tau turning F into the product of the axioms of its proof; A_tau
    opens the brackets of ~F v G accordingly (Lemmas 12, 17, 18); Lemma 15
    then removes the false constants (Lemma 14) and the pairs A ~A (atomic
    cuts, Lemma 13).  Coquand's Proposition 2 performs the same steps one
    focus of the proof of F at a time.  Neither argument uses induction on
    the cut formula.
  - The calculus is a sequent calculus with cut, not Novikov's axioms 1-3
    and rules 4-6.  Axiom 3 and rule 6 are foci, and rule 5 is mp.  The
    finitary tautologies (axiom 2) are not formalised.
