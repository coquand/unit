# Loader's CC machine, HOL Light and Unit

1 November 2026. The source of `loader.c` (Ralph Loader, winner of David Moews'
Bignum Bakeoff, 2001) is the entry `{loader.c}` of
<http://djm.cc/bignum-results.txt>: 512 characters, whitespace excluded.
`Loader.hs` (this directory) is a reading of it in Haskell, with tests.

## What loader.c is

It is not a checker of given terms. It is a **machine that produces judgements
of the Calculus of Constructions by rules**, steered by the bits of a number. In
that respect it is an LCF kernel like HOL Light: a judgement exists only because
a rule made it.

- **Codes.** A positive integer is uniquely P(y, x) = (2y+1)·2^x. A term is
  P(tag, payload): tag 0 is Π, tag 1 is λ, tag 2 is application, and the payload
  is P(domain or function, body or argument). The sorts are * = 7 and □ = 14,
  and variable i (de Bruijn) is P(4+2i, 0). A context is a list of types, built
  with P.
- **Substitution `S(v,y,c,t)`.** It replaces variable v by y; variables above v
  move down when c = 4 (β) and up when c = −4 (shift, `S(4,13,−4,·)`). At an
  application it calls `A`.
- **Application `A(y,x)`.** If y is a λ, it substitutes x into the body;
  otherwise it builds the application. So substitution is hereditary and every
  term stays β-normal.
- **The machine `D(x)`.** Its state is (Γ, t, u), meaning Γ ⊢ t : u, and it
  starts at ⊢ * : □. Each round reads bits of x. A sub-derivation is read from the
  following bits (`D(x)` on the rest), and each rule fires when its bit is set:
  - **application:** Γ ⊢ t : Πx:A.B and Γ ⊢ d : A give Γ ⊢ t d : B[d/x];
  - **weakening:** Γ ⊢ t : u and Γ ⊢ d : s give Γ, d ⊢ t↑ : u↑;
  - **abstraction:** Γ, A ⊢ t : u gives Γ ⊢ λA.t : ΠA.u;
  - **product:** Γ, A ⊢ t : s gives Γ ⊢ ΠA.t : s;
  - **variable:** Γ ⊢ t : s gives Γ, t ⊢ 0 : t↑.
  Every call pushes its judgement on a global stack `a`, which is the output.
  The calls `D(x−1)` in the loop condition only feed this stack, so it ranges
  over all smaller programs. The printed number is the stack after
  D(D(D(D(D(99))))).
- **Conversion is `==`.** Since all terms are normal and use de Bruijn
  indices, the two conversion tests (equal contexts; domain = type of the
  argument) are integer equality. There is no conversion rule and no
  normaliser apart from hereditary substitution.

## What was checked

`Loader.hs`: (1) the C program on the free pairing algebra (numbers as trees
of P, so the tower-sized stack is representable); (2) the same machine on a
datatype of CC terms; (3) an independent textbook checker for CC (ordinary
substitution, conversion by full normalisation).

    ghc -O1 -o loader-hs Loader.hs -outputdir build && ./loader-hs 16 1048576

- (1) and (2) agree, judgement and whole stack, for x ≤ 16. (The stack grows
  too fast to compare beyond that.)
- For every x ≤ 2^20 the judgement (176 distinct ones) has a normal term and a
  normal type, and is accepted by the checker (3), with one qualification:
- **45,402 of them are not CC judgements.** The abstraction rule fires
  whenever u is not a sort, and also when u = □ on a set bit, so it gives for
  instance ⊢ λx:*.* : Πx:*.□, and Πx:*.□ has no type in CC. All of them are
  accepted once one more universe □ : △ is added, with Π-rules (s₁,s₂,s₂) for
  all three sorts. That system is a fragment of the Calculus of Constructions
  with universes of Coquand, *An analysis of Girard's paradox* (LICS 1986)
  (Prop, Type₀, Type₁; later extended by Luo's ECC), so it is still strongly
  normalising, and termination of the program is not
  affected. Strictly, loader.c is a machine for CC with type-level λ over kinds.

## Comparison

Code lines are non-blank and non-comment. HOL Light is `fusion.ml` (GitHub
master, 1 November 2026), and Unit is the trusted part of `unit/src` (see the
count in the conversation of 1 November: §§1–6 and 8–11 of `Seg.hs`, plus
`Level.hs` and `Term.hs`; hidden arguments, quoting, printing, parser and driver
excluded).

| | loader.c | HOL Light kernel | Unit trusted core |
|---|---|---|---|
| size | 512 chars; 60 lines of Haskell (§2) | 400 lines OCaml | ≈1,680 lines Haskell |
| logic | CC (+ λ over kinds) | HOL (simple types) | MLTT: Π, Σ, records, sums, Id/J, universe levels with constraints, segments |
| kind | rule machine (LCF style) | LCF: abstract `thm`, 10 rules | checker of explicit terms |
| terms | always normal | arbitrary | arbitrary, with definitions |
| conversion | code equality | `BETA` as a rule; definitions are equations | evaluation, lazy unfolding, names first, locks |
| proof objects | none (the bits) | none | the terms |

Two numbers isolate where Unit's size goes:

- A **checker** for given CC terms, which loader.c does not need, is 55 lines
  (§3 of `Loader.hs`). So "dependent types with conversion" alone costs about
  as much as loader.c's machine.
- Unit is about 30 times that, and the factor goes to what the mathematics
  uses and CC lacks:
  - definitions that are unfolded only on demand, compared by name first
    (`Seg.hs` §§3–5, about 600 lines; this is what keeps files under 1 s);
  - universe levels with constraints and the loop check (about 105 lines of
    `Level.hs`, plus their checking);
  - records, labelled sums with positivity, and Id/J;
  - the segment module system with sharing by name (§§10–11).

loader.c's main idea, keeping every term normal so that conversion is
equality, is not available to Unit: its developments rely on *not*
normalising.
