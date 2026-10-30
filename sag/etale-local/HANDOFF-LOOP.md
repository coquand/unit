# Handoff: the loop Q_0, Q_1, ... of zmt2-revised.tex Section 1 (remainder version)

Directory: `unit/sag/etale-local` (README.txt there: §4, Lemmas 1, 2 done).
Check: `./segc sag/etale-local changed` (from `unit/`), every shell command
under 60 s, read `/Users/coquand/CANONICITY/seg/WRITING.md` before writing,
audit with `seg All.seg --only M --opened`.  No ring solver: identities by
short named lemmas.

## Statement (independent of ZMT and of the special fibre)

Data.
- `R` commutative, `m` an ideal of `R` (predicate with 0, +, scalar
  closure), residually discrete: `dec : (a : R) -> m a + unit a`, and
  `rad : m a -> unit (1 - a)` (local).
- `B` commutative, `iota : R -> B`, `y : B`.
- A monic relation of degree `e0`: `a0` with `y^e0 = [a0]_e0 (y)`.
- `W in R[X]` (a coefficient list) with `W(y) in m R[y]`, i.e.
  `W(y) = sum_j iota(mu_j) R_j(y)`, `mu_j in m`, `R_j` coefficient lists.

Notation. For `e : Nat`, `c : Nat -> R`: `[c]_e = sum_{i<e} c_i X^i`
(in `R[X]`, and its value `sum_{i<e} iota(c_i) y^i` in `B`).  A monic
relation of degree `e` is `a` with `y^e = [a]_e(y)`; `Q = X^e - [a]_e`.
`x in_Q m` means `x = sum_{i<e} iota(mu_i) y^i` with every `mu_i in m`.

Conclusion. A monic relation `Q` of degree `d <= e0` (so `Q(y) = 0`), and
`U in R[X]`, `c` with every `c_i in m`, such that `W = U Q + [c]_d` in
`R[X]`: Q-bar divides W-bar in k[X].  (In the note `W = G^n H`.)

## Informal proof

Lemma A (reduction modulo a monic Q of degree e >= 1).  Every `F in R[X]`
given by coefficients is `U Q + [c]_e`.  Horner: `F = f0 + X F1`,
`F1 = U1 Q + [c']_e`.  `X [c']_e = [shift c']_(e+1) = [shift c']_e + c'_(e-1) X^e`
and `X^e = Q + [a]_e`, so `F = (X U1 + c'_(e-1)) Q + [f0 + shift c' + c'_(e-1) a]_e`
(`shift c' 0 = 0`, `shift c' (i+1) = c' i`; `f0` added at index 0).
(e = 0: Q = 1 and y^0 = [a]_0(y) = 0 means B is trivial; the loop stops.)

Lemma B (`in_Q m` is an R[y]-submodule).  Closed under +, `iota(r) .`,
and `y .` (shift, then `y^e = [a]_e(y)`: new coefficients
`shift mu + mu_(e-1) a`, still in m).  Hence `F(y) x in_Q m` for every F
(Horner), and the hypothesis on `W(y)` gives `W(y) in_Q m`.

One step.  `Q` monic of degree `e >= 1`, `W(y) in_Q m`.
1. Lemma A: `W = U Q + [c]_e`, so `[c]_e(y) = W(y) in_Q m`.
2. Scan `c_(e-1), .., c_0` with `dec`.  If all are in m: STOP with (Q, U, c).
   Otherwise `d < e` is the top index with `c_d` a unit, `c_i in m` for
   `d < i < e`.
3. `D = X^d + [c_d^-1 c]_d` is monic of degree d and
   `D(y) = c_d^-1 ([c]_e(y) - sum_(d<i<e) c_i y^i) in_Q m`.
   So `y^d = -[c_d^-1 c]_d(y) + (in_Q m)`.
4. For every j: `y^j = [beta_j]_d(y) + (in_Q m)` (induction on j; j < d
   trivial; `y . ` preserves the shape using 3 for the overflow `y^d`
   and Lemma B for the m-part).
5. Nakayama.  For `j < e`: `y^j = [beta_j]_d(y) + sum_(i<e) iota(mu_ji) y^i`,
   i.e. `(I - mu) v = n` with `v_j = y^j`, `n_j = [beta_j]_d(y)`.
   `u = det(I - mu) = 1 mod m` (ExteriorRelation with `a ~ c iff a - c in m`),
   a unit by `rad`; `u v_k = sum_j adj(I-mu)_jk n_j` (as `det-times` in
   DeterminantLemma, with `Map.adj-map` for iota).  So
   `y^k = [sum_j u^-1 adj_jk beta_j]_d(y)` for all `k < e`.
6. `k = d` gives the new monic relation `Q'` of degree `d < e`; the same
   formulas move `W(y) in_Q m` to `W(y) in_Q' m`
   (`sum_i iota(mu_i) y^i = sum_l iota(sum_i mu_i gamma_il) y^l`).
Loop: recursion on a fuel `e0`, invariant `deg Q <= fuel`.

Relation to the note.  The note takes `D_l = gcd(Q_l-bar, G^n H-bar)` with a
Bezout identity.  Here `D_l` is the normalised remainder of W modulo Q_l:
`D_l-bar` is in the ideal (Q_l-bar, W-bar), so `D_l(eta) = 0` as in the
note, and the loop performs Euclid's algorithm itself.  The output used in
§2 (Q(y) = 0, Q-bar | G^n H-bar) is the same.  `H-bar | Q-bar` needs the
special-fibre iso and is not part of the loop.

## Formal plan (files, in order)

1. `PowerSums.seg`: `psum e c` in any comm. ring with an element t:
   `psum zero c = 0`, `psum (suc e) c = add (mul (c e) (t^e)) (psum e c)`
   (matches `FiniteIdeal.Sums.sum` order: `inr tt` = top index e).
   Lemmas: add, scale, shift (`t . psum e c = psum (suc e) (shift c)`),
   ring maps (`phi (psum e c) = psum e (phi c)` at `phi t`), and
   `psum e c = S.sum e (\ i -> c (nat i) t^(nat i))` for the Fin index
   `nat : Fin e -> Nat` (inr tt |-> e-1 ... chosen to match).
   Use it in R[X] (t = X, constants) and in B (t = y, iota).
2. `MonicReduce.seg`: Lemma A in R[X] (CharPoly's `CP.B` = PolynomialRing).
3. `MPart.seg`: `in_Q m` and Lemma B.
4. `TopUnit.seg`: the scan of step 2 (recursion on e, like
   ResidualIdempotent.strip but from the top).
5. `LoopStep.seg`: steps 3-6.
6. `Loop.seg`: the fuel recursion and the theorem.

## Status

Done and checking (2026-10-30): `PowerSums.seg` (psum, Coef.shift/point,
cong, zero, add, scale, shift, point, Map.psum-map) and `MonicReduce.seg`
(Lemma A, generic over an A-algebra T with t; `Over[A,T,kappa,t,e',a]`,
`Q = t^e - P a`, `horner`, `reduce : (fs) -> Reduction (horner fs)`).
Pitfall: never call the base ring `R` in a module that does `open T`
(the opened carrier `R` clashes); call it `A`.

DONE 2026-10-30 (later the same day): MPart, LoopStep, LoopNakayama, Loop
all written and checking (58 modules, 0 failed, 0.4 s); Loop.Over.theorem
is the statement above.  Open: package a general certificate
sum mu_j R_j(y) into InM (MPart closure under Horner multiplication);
the residual quotient openings listed in README.txt.

Q' step DONE too: DerivativeStep.seg (derivative via dual numbers,
Qprime.result) and LoopQprime.seg (Section1: loop + Q' step); 62 modules.

## Refined design for steps 2-6 (as built)

Work in B with `V_e c = PowerSums.Over[B,y].psum e (\ i -> iota (c i))`.
- `InM e x = (mu : Nat -> A) * ((i : Nat) -> m (mu i)) * Id x (V_e mu)`:
  coefficients in m at ALL indices (no bounded quantifiers).  Closure
  under 0, +, neg, iota(r)., and y. (needs the relation y^e = V_e a,
  e = suc e': y V_e mu = iota(mu e') y^e + V_e(shift mu)).  Hence
  `iota(c) y^i in InM` for c in m and every i (induction on i, base
  V_e(point c)).
- Step 1 in R[X] (MonicReduce with T = R[X], t = X, kappa = constants),
  evaluated by ev (PowerSums.Map, ev Q = 0) to get V_e c = W(y).
- Scan (step 2), recursion on e, using `dec` on c e:
  `Below zero c = Top`, `Below (suc e) c = m (c e) * Below e c`;
  result `Plus (Below e c) Found` with Found = d, `Le (suc d) e`
  (recursive Le), unit (c d), x with InM_E x and
  `V_e c = iota(c d) y^d + V_d c + x` (the m-part as an ELEMENT; the
  dropped terms iota(c_i) y^i are added one at a time).
- Step 3: `y^d = V_d(beta) + x'`, beta = -(c_d^-1) c, x' in InM.
- Step 4: `SpanM d z = (beta) * (x) * InM x * z = V_d beta + x`; all y^j
  are SpanM (induction on j; base j = 0 splits on d: d = 0 uses step 3,
  d = suc d' uses point o).
- Step 5: `nat : Fin E -> Nat` (inr tt |-> E-1 ... matching psum's order);
  lemma `psum e c = S.sum e (\ i -> c(nat i) t^(nat i))`;
  matrix `M j i = delta_ji - mu_i(nat j)` over A, `det-times` as in
  DeterminantLemma (in B with iota M, Map.adj-map, det-nat),
  `det M = 1 mod m` by ExteriorRelation with `a ~ c iff m (a - c)`,
  unit by `rad`.  Gives `y^(nat k) = V_d(gamma_k)` for all k.
- Step 6: `fin-of : Le (suc d) E -> Fin E` with `nat (fin-of) = d`; new
  relation gamma at degree d; transfer W(y) to InM_d.
- Loop on fuel f with `Le e f`; e = 0 stops at once (Q = 1, Below 0 = Top).
  `Qpoly e a = X^e - [a]_e` in R[X] (definitionally MonicReduce's Q for
  e = suc e').  Result: e, a, y^e = V_e a, U, c, Below e c,
  W = U Qpoly + [c]_e in R[X].
