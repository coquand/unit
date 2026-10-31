# Handoff: closing Theorem `local` of zmt2-revised.tex (blocks 1 and 2)

Source note: `~/COLL/zmt2-revised.tex`.  Directory: `unit/sag/etale-local`
(read `README.txt` first; `HANDOFF-ETALE-CASE.md` is the previous step,
Stage A done).  State at handoff (2026-10-30): `./segc sag/etale-local all`
(from `unit/`) = 74 modules, 0 failed, 0.63 s.

Goal: Theorem `local` (note line 61): R residually discrete local, E etale,
q a decidable prime of E containing m E; there is s not in q with E[1/s]
standard etale.  Everything except the hypotheses listed below.

## Rules (user rulings, all apply)

- Read `/Users/coquand/CANONICITY/seg/WRITING.md` before writing: informal
  proof at the head of each file, one name per notion (no aliases), "by
  definition" facts as `refl` lemmas next to the definition, write the
  common point of a definitional step, accessors rather than `.2.2.1`.
  Audit each new file with
  `SEG=$(cabal list-bin exe:seg); cd sag/etale-local; $SEG All.seg --only M --opened`
  (a declaration opening more than its text names is a defect, even fast).
- Every shell command under 60 s (`timeout 55`); check with
  `./segc sag/etale-local changed`, `all` only at the end;
  `./segc sag/etale-local stop` after.
- No ring solver: ring identities by short named lemmas (RL[..]:
  add-neg-cancel, neg-uniq, neg-neg, mul-swap, add-swap, swap, dist-left,
  zero-mul, mul-zero, one-left, neg-mul-left, mul-neg, negsub, mul-four,
  zl; FormallyEtale.Units: unit-prop/mul/left/right, sub-zero,
  idempotent-one).
- Report "no new axioms" (Theory parameters univalence + replacement).
- Pitfalls met: never name the base ring `R` in a module that `open`s
  another ring (use `A`); `U` is reserved and `Universal` is a module name
  (no shadowing); parameterised records are written `SquareZero[B]`;
  `where` blocks cannot contain modules; give hidden arguments explicitly
  when inference fails; apply a module to the SAME expressions everywhere
  (`Fractions[Q,G,S,s]` with `s = st.1` against `Fractions[..,st.1]`
  made the checker open evaluation internals); new files go into `All.seg`
  after their dependencies; library files enter as relative symlinks.

## Hypotheses that stay hypotheses (do not prove)

- ZMT (ACL Cor. 1.4): a finite R-subalgebra B of E (R-module generators
  b_1..b_r, multiplication table) and s in B, s in 1 + m E, with
  B[1/s] = E[1/s].
- Field case: E/mE (and A[1/s-bar], A = B/mB) finite etale over k, a
  finite product of monogenic k[X]/(P), P monic separable; decidable
  equality in these k-algebras.
- q decidable, k = R/m discrete (as `dec`/`rad` in Loop/Section1Eg).
State each as a parameter in the note's form, with a comment.

## Block 2 first: the Introduction steps (note lines 75-158, 159-200)

Produce, from the hypotheses, exactly the inputs of
`Section1Eg.Over[..].Section1[n',a,bs,eq,c,one,g,h,gu,full,hH,hH']`:
integrality data (n', a, bs, eq, c, one), G (list g) with G(y) a unit,
`full` (E_g = R[y][1/g], ClearDenominators.Full), H (list h) with
H(y) in m E_g (hH) and H'(y) a unit mod m E_g (hH').
Steps of the note:
1. Lemma 1 (done: ResidualIdempotent) gives e-bar idempotent with
   A[1/e-bar] = A[1/s-bar]; choose the monogenic factor containing the
   prime induced by q, lift its idempotent, refine s (lines 85-90).
2. x-bar with x-bar e-bar generating A e-bar, x-bar not in the prime (else
   x-bar - 1); A e-bar = k[X]/(P); y-bar = x-bar e-bar, y-bar A in k[y-bar]
   (lines 112-129).  Lift y-bar to y in B: y B in R[y] + m B.
3. Lemma 2 (done: DeterminantLemma, System/Generated/Congruence/Prime):
   p in R[y] not in q with p B in R[y]; g = s p, E_g = R[y][1/g], g not in q
   (lines 136-158).  This gives `full` and G.
4. Special fibre (lines 159-200): H-bar = P/gcd(P,X), H a monic lift,
   C[1/G-bar(eta)] = k[X]/(H-bar); H(y) in m E_g with certificate (from the
   field case), H'(y) a unit mod m E_g (separability).
Decide first how much of 1-2 and 4 is a consequence of the field-case
hypothesis as stated, and phrase that hypothesis so the steps are short;
say in the file comment what is assumed.  Integrality data for y: from
the generators of B (y b_i = sum_j b_j a_ji, 1 = sum c_k b_k), as
`LoopInputs.Integral` expects.

## Block 1: Stage B of Section 2 (HANDOFF-ETALE-CASE.md, Status)

Inputs of `EtaleCase.Over[A,setA].Section2[S,T,u,surj,surj-eq,r,k,k-in,gen]
.Theorem[Q,G,st,full,lift].local`:
(a) S standard for (Q, G) with `Fractions[Q,G,S,s].Full`: build S, e.g.
    `presentations/PresentedAlgebra` (its Presentations/Algebras are the
    same files as here) with variables X, V and equations Q(X),
    (G Q')(X) V - 1, needing RX polynomial -> Expr; or directly.  Prove the
    universal property (push is an equivalence) and Full (P(X,V) =
    sum P_k(a) w^k = P'(a) w^K).
(b) u : S -> T, T = E[1/g_1], g_1 = g Q'(y), X |-> y: Q = Section1.S1.S1.Q,
    G = LI.Ho.horner g; Q(y) = 0 is `root`, (G Q')(y) a unit in T.  Needs a
    bridge lemma: DerivativeStep.der Q = StandardEtale At[..,y].derivative Q
    (both are the dual-number evaluation; by Universal uniqueness).
(c) surj: T = R[y][1/g Q'(y)] from ClearDenominators.Full.
(d) generators of ker u from a presentation x_i, f_j of E with
    x_i = sigma_i(y) (Full) and y = Y(x): ker u = (f_j(sigma(a)),
    a - Y(sigma(a))), proved by the inverse map T -> S/K.
(e) lift : E.Lift T from Lift E (lift, then FormallyEtale.unit-mod-nilpotent
    for g_1).  Uniqueness of T is not needed.
(f) the final statement: s = g g_1 not in q (g not in q from step 3;
    Q'(y) not in q from DerivativeStep.Qprime.outside) and E[1/s] = T
    standard for (Q, G F), under the truncation of EtaleCase.Theorem.local.
    Write it as `Local.theorem` in a new file, with the hypotheses of the
    section above as its only parameters besides E, q.

## Status

**Block 2: done (2026-10-30).**  `./segc sag/etale-local all`
= 77 modules, 0 failed, 0.64 s (standalone `seg All.seg`: 3269
declarations, 0.97 s).  No new axioms (Theory parameters univalence +
replacement); `--opened` audited for the three new files.

New files (README.txt, section "THE INTRODUCTION"):
- `IdempotentModM.seg`: Lemma 1 modulo an ideal I containing m (strip,
  idempotent/e-one/kill modulo I, horner-monic).
- `HornerValues.seg`: Horner values of lists: sums, products, ring maps,
  congruence modulo an ideal, `Shifts[A].sh` (X |-> X + 1).
- `Introduction.seg`: the hypotheses and steps 0-4.

Hypotheses as stated (`Introduction.Over` and `.FieldCase`):
- ZMT after the refinement: B an A-algebra with an algebra map
  `j : B -> E`, generators `bs` with `coord`, `s` with `s-out` and
  `zmt : s^k z = j(b)`.  (Step 1 of the note, the choice of the factor and
  the refinement of s, is inside this hypothesis.)
- Field case, `Factor x0`: P with `root` (s^N P(x) in m E), `separable`
  (s^N (P'(x) w - 1) in m E, P' = slope, the epsilon-component), and
  `generates` (every b: s^N (b - C(x)) in m B).  Only these consequences
  of A[1/s] = k[X]/(P) are used (no monicity, no injectivity).
- q prime, containing m E, decidable (`q-dec`, used for x vs x - 1).

Decisions (differ from this handoff's plan; say so to block 1):
1. **Section 1 runs in E, not in E_g.**  `Section1Eg` wants `full` as
   untruncated data, but on a constructed E_g (a quotient) fractions exist
   only merely.  So `LoopInputs.Section1` is applied with B := E and
   J := `Jsat` = { w | g^k w in m E } (the note's m E_g read in E); J is
   contained in q (`q-J`).  `Section1Eg` is not instantiated.
2. **H = P** (no gcd with X): the loop needs only H(y) in J and H'(y) a
   unit mod J.
3. **Mere existence.**  The polynomials F_k of Lemma 2 (p b_k = F_k(y)) live
   in the quotient A[X]; lists are chosen for them (`Main.choice :
   ||Main.Choice||`, finite choice).  Everything downstream is in
   `Main.Chosen[FL]` for an arbitrary choice FL; block 1 eliminates
   `FieldCase.choice` into its (propositional) goal.

What block 1 gets, in `FieldCase[x0,F0].M.Chosen[FL]` (E is the ring,
the point is `j.1 y`):
- `G` (list), `gE = G(y)`, `g-out : Not (q gE)`, `full : CDE.Full G`
  (every z in E: z g^k = r(y)), `Jsat` with its laws and `q-J`;
- `S1 = LIE.Section1[..]`: `S1.S1.Q` (monic Q), `root-Q` (Q(y) = 0),
  `S1.S1.divides` (G^n P = U Q + [c]_e), `Qprime = S1.LQ.DS.der S1.S1.Q`,
  `Qprime-unit` (unit mod J), `Qprime-out : Not (q Qprime)`;
- from `M`: `y-out` (j y not in q), `p-out`, `SYS` (Lemma 2 data).
Block 1's item (c) can use `full` (in E) directly; item (b) needs the
bridge between `DerivativeStep.der` (here `S1.LQ.DS.der`) and
`StandardEtale` derivative as planned.

**Block 1: done (2026-10-30).**  Theorem local is
`Local.Over[..].Field[x0,F0,etale].theorem : || Conclusion ||` with
Conclusion = (s' : E) * s' not in q * (T, i : E -> T) * IsLocalisation T i s'
* (Q, G) * T standard for (Q, G).  `./segc sag/etale-local all` = 88
modules, 0 failed, 0.90 s (standalone 3846 declarations, 1.34 s).  No new
axioms; hypotheses: the Introduction's plus `etale : FormallyEtale.Etale E`.

How the items were done:
- (a) `StandardAlgebra.Build`: S presented (A[X0]/(Q(X0)), then
  `affine/Localization` at g(X0)); `standard` from the universal
  properties; `full` from `Generated` (fractions closed under +, *).
  Lists for Q and G Q' are chosen (mere).
- (b) T = `Localization` of E's presentation at g1 = (G Q')(y)
  (`g1-split`: = g Q'(y)); u = the inverse of push at the point y.
- (c) `surj` is MERE: preimages of the generators of T (PreE from
  `Chosen.full`, and 1/(G Q')(s)), then `Generated`.
- (d) kernel generators f_j(sigma(s)) and s - Y(sigma(s)) (Y a chosen
  expression of y); `psi : T -> S/K` (K = RegularIdeal.Generated),
  `psi-u`, `gen` (mere).
- (e) `lift-T` from the lifting of E and `unit-mod-nilpotent`.
- (f) `EtaleCase.Theorem.local`.
Interface change, as anticipated: `EtaleCase` (Surjection, Section2,
Fractions.Full, Localised) and `IdempotentIdeal` now take mere `surj`,
`gen` and `Full` (a quotient-built S, T only has these merely).
`--opened` audited; the remaining larger openings are definitional
bridges (evaluation at y in Loop vs StandardEtale, `Qprime-is` for the
dual-number derivative, `push-at`, `map-at`, `compose-at`) and type
formers.

**Hypotheses in the note's form: done (2026-10-30).**
`TheoremLocal.Over[.., s, s-one, zmt, etale].FieldCase[nf, eps, sum-one,
xs, pieces].theorem` states Theorem local with ZMT as in ACL (s in
1 + m E) and the field case as a decomposition into factors
A[1/s-bar] eps_i = k[X]/(P_i) (only sum eps_i = 1 in (E/mE)[1/s] and the
facts of each factor are used).  It does note lines 85-90: s not in q,
choice of a factor outside q by decidability of q, refinement s' = s eps_i,
then `Local.Field.theorem`.  `Local`'s conclusion now lives in
`Local.Statement` (independent of s).  89 modules, 0 failed, 0.96 s
(standalone 3944 declarations, 1.36 s).  What is left: ZMT and the
structure theorem for finite etale algebras over a discrete field.
