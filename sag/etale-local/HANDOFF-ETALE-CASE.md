# Handoff: Section 2 of zmt2-revised.tex, "What happens if E is étale" (lines 296-326)

Source note: `~/COLL/zmt2-revised.tex` (Introduction lines 33-46 for the
definitions; Section 1 lines 248-272 for the surjection u; Section 2 lines
296-326).  Directory: `unit/sag/etale-local` (read `README.txt` first;
`HANDOFF-ITEM4.md` is the previous step, done).
State at handoff (2026-10-30): `./segc sag/etale-local all` (from `unit/`)
= 67 modules, 0 failed, 0.51 s.

## Rules (user rulings, all apply)

- Read `/Users/coquand/CANONICITY/seg/WRITING.md` before writing: informal
  proof at the head of each file, one name per notion (no aliases), "by
  definition" facts as `refl` lemmas, write the common point of a
  definitional step, accessors / named arguments rather than `.2.2.1`
  chains.  Audit each new file with
  `SEG=$(cabal list-bin exe:seg); cd sag/etale-local; $SEG All.seg --only M --opened`.
- Every shell command under 60 s (`timeout 55`); check with
  `./segc sag/etale-local changed`, `all` only at the end;
  `./segc sag/etale-local stop` after.
- No ring solver: ring identities by short named lemmas (RL[..]:
  add-neg-cancel, neg-uniq, neg-neg, mul-swap, add-swap, swap, dist-left,
  zero-mul, mul-zero, one-left, neg-mul-left, mul-neg, negsub, mul-four, zl).
- Report "no new axioms" (Theory parameters univalence + replacement).
- Pitfalls met: never name the base ring `R` in a module that `open`s
  another ring (use `A`); `where` blocks cannot contain modules; give
  hidden arguments explicitly when inference fails; add new files to
  `All.seg` after their dependencies; new library files enter as relative
  symlinks (as `FiniteIdeal.seg -> ../exterior/FiniteIdeal.seg`).

## The definition of étale (DECIDED)

Use the note's own definition (Introduction): **E is étale if it is finitely
presented and formally étale: R-algebra maps into a quotient by a
square-zero ideal lift uniquely.**  Unramified = the uniqueness half.

Reasons: it is the note's definition; the proof of Section 2 uses exactly
its two halves (existence for T, uniqueness for S); "finitely presented" is
used only to know that the kernel of u is finitely generated.  The
Jacobian definition (Lombardi-Quitté; `sag/etale-flat` uses the Jacobian
`RegularPolynomial.j`) would add a Jacobian criterion that the note does
not use.  Jacobian => formally étale (one Newton step in a square-zero
extension) is a possible later bridge to `sag/etale-flat`, not part of this.

Formal shape (over `Algebras[l].Over[R,setR]`, R the note's base ring):
- a square-zero ideal of an algebra C: a membership predicate N on C.ring
  with the ideal laws, propositional membership, and `a, b in N -> a b = 0`;
- `C/N` as an algebra: `cffr/QuotientRing.seg` (Over[Rg,I,prop], ideal
  given as `RegularIdeal.IdealPred`; link `QuotientRing.seg` and
  `RegularIdeal.seg` and whatever they import) with its projection `pi`;
- `Lift E` : every `Hom E (C/N)` is `pi o h` for some `h : Hom E C`;
  `Unique E` : `pi o h = pi o h'` implies `h = h'`;
  `FormallyEtale E = Lift E * Unique E` (state each half separately: the
  proof uses them separately);
- `Etale E = FormallyEtale E * Witness E` (Presentations.Witness: a
  presentation P and `Presents P E`).  In Stage A the witness is not used.
- Comment in the file: via `Presents`, `Hom E (C/N)` is the type of
  solutions of the equations modulo N, so the definition is the usual one
  in points form ("a solution mod a square-zero N lifts uniquely").

Check before writing: `etale-local/Presentations.seg` links to
`../pn/Presentations.seg`, `fpalg` uses `../presentations/Presentations.seg`.
Find out whether `presentations/PresentedAlgebra.seg` can be used against
the etale-local `Presentations`/`Algebras` (same declarations?) or whether
S must be built otherwise (e.g. `horrocks/MonoidLocalization.seg` on the
quotient of A[X] by Q, or directly by points with a universal property).
Decide this first; it fixes how S is a ring.

## Informal proof to formalise (note, Section 2)

Data: u : S -> T a surjective R-algebra map, S standard étale,
S = (R[X]/(Q))[1/(G(a) Q'(a))], T = E[1/g_1] étale.  I = ker u, finitely
generated: I = (k_1, .., k_r).

1. (S unramified.)  Two algebra maps h, h' : S -> C with pi h = pi h'
   (N square-zero) are equal.  They are given by points a, a' (Q(a) = 0,
   G(a)Q'(a) a unit, same for a') with eps = a' - a in N, so eps^2 = 0.
   The map C[eps]/(eps^2) -> C, eps |-> a' - a, is a ring map; pushing the
   dual-number evaluation of `DerivativeStep` / `QuadraticPairs` (val, der)
   through it gives Q(a') = Q(a) + Q'(a)(a' - a).  So Q'(a)(a' - a) = 0 and
   a = a' since Q'(a) is a unit.
2. (I = I^2.)  C = S/I^2, N = I/I^2 (square-zero).  T = S/I (u surjective,
   kernel I) maps to C/N = S/I; by Lift for T get sigma : T -> S/I^2 with
   pi sigma = that map.  The projection p : S -> S/I^2 and sigma u agree
   after pi; by 1 they are equal.  For i in I: p(i) = sigma(u(i)) = 0, so
   i in I^2.  With generators: k_j = sum_l a_jl k_l, a_jl in I.
3. (Idempotent.)  f = det(delta_jl - a_jl): f I = 0 and f = 1 mod I, so
   1 - f in I, f(1 - f) = 0, f^2 = f, I = (1 - f).  Reuse the determinant
   trick (`DeterminantTrick`, as `LoopNakayama` does).
4. (S[1/f] = T.)  In points form: Hom T C is equivalent to the points a of
   S in C with f(a) a unit (u o -, using I = (1 - f): a point of S kills I
   iff it sends 1 - f to 0 iff f(a) is a unit, f being idempotent).
5. (Principal localisation.)  Write f = F(a)/(G(a)Q'(a))^r; S[1/f] is the
   standard étale algebra with G replaced by G F (points: same Q, and
   (G F)(a) Q'(a) a unit).  Hence T standard étale: Theorem `local`.

## Plan

Stage A (this session): Section 2 from named inputs.
1. `FormallyEtale.seg`: square-zero ideals, C/N (QuotientRing link),
   Lift, Unique, FormallyEtale, Etale (definitions + the points-form
   comment); `unit-mod-nilpotent`: x a unit mod a square-zero N is a unit
   ((x v - 1)^2 = 0 gives x v (2 - x v) = 1).
2. `StandardEtale.seg`: S for (Q, G) monic Q, its points, `unramified`
   (step 1), `localise` (step 5).  Optional: `lift` (S étale: Newton step
   a' = a - Q(a) w, w an inverse of Q'(a) mod N), stated as in the note's
   "Such an algebra is étale by the simple-root lifting argument".
3. `IdempotentIdeal.seg`: finitely generated K with every generator in K^2
   (certificates a_jl in K) gives f with f^2 = f, f K = 0, 1 - f in K
   (step 3).
4. `EtaleCase.seg`: Over the data u : Hom S T, `surj` (a preimage
   function), generators k_1..k_r of ker u with membership certificates
   (hypothesis: "S and T finitely presented, so ker u finitely
   generated" -- say so in the comment), `liftT : Lift T`:
   `I-idempotent` (step 2), f, `points` (step 4), `standard` (step 5):
   T is standard étale.
5. Connect to Section1Eg in the README: S is built from S1.Q and G; u is
   a |-> y; T = B[1/Q'(y)] -- state what remains to plug them together
   (Stage B).  Update README.txt and this file's Status.

Stage B (later, not this session): discharge the inputs from a
presentation of E: (a) T = E[1/g_1] formally étale from E (lift, then
`unit-mod-nilpotent` for g_1); (b) generators of ker u from the
presentation x_1..x_n, f_1..f_m of E, `Full` (x_i = sigma_i(y)) and
y = Y(x): ker u = (f_j(sigma(a)), a - Y(sigma(a))), proved by the inverse
map T -> S/K; (c) u from Section1Eg's data (S1.Q, G, Q'(y) unit).

Remain hypotheses (do not do): ZMT (ACL Cor 1.4), the field case (E/mE a
product of monogenic separable k-algebras), the special-fibre facts of
Section1Eg.

## Status

2026-10-30: Stage A DONE.  `./segc sag/etale-local all` = 74 modules, 0
failed, 0.63 s.  New files: FormallyEtale,
StandardEtale, IdempotentIdeal, EtaleCase (statements in README.txt);
links QuotientRing, RegularIdeal (cffr), TruncationCombinators
(replacement).  No new axioms (Theory parameters univalence +
replacement).  --opened audited: each declaration opens only the
definitions its text names, apart from projections of Hom/Point types.

Decisions taken in Stage A:
- S is given by its universal point (Points[Q,G].Standard: push h = h(s)
  is an equivalence onto the points), not constructed; "T standard etale"
  is the same structure for (Q, G F).  presentations/PresentedAlgebra can
  build S in Stage B (its Presentations and Algebras are identical files).
- Full (every x of S is P(s)/g^n) is an input on S; only f needs it.
- I^2 membership is a truncated certificate (QuotientRing needs
  propositional membership), so the final result is a mere existence
  || (F : A[X]) * T standard for (Q, G F) ||; finite choice over Ps.Fin is
  EtaleCase.choice.
- N = I/I^2 is the (truncated) image of I in S/I^2; C/N -> T is not built,
  only v : T -> C/N, the factorisation of S -> C -> C/N.
- Only Lift T is used (Theorem takes `lift : E.Lift T`); S unramified is
  StandardEtale.unramified.
- Q' is the polynomial deriv Q (derivative at the variable of A[X]);
  deriv-value relates it to the dual-number derivative at any point.
Optional item not done: S etale (Newton lift a' = a - Q(a) w).
Next: Stage B, inputs listed at the end of the Section 2 part of
README.txt.
