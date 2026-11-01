# Handoff: WA.seg, Section 4.3 DONE

State (2026-10-27): `WA.seg` green (797 declarations with imports, 0.25 s),
`segd WA.seg --opens WA.opens`: all 35 declarations listed, nothing else
opened. No postulates; hypotheses are Setzer's (and fewer for 4.13(c)).

Done: Def. 5.6 (TH, W1, idx, Cor by the recursion of Remark 5.7(c), WA),
Assumption 4.10 (wa-a, wa-b), Notation 4.11 (wa-ind), Def. 4.12 (Bar, Seg),
Lemma 4.13 (a)-(d). Use downstream: wa-a, wa-ind (= Ind(x in W(A))), wa-M,
wa-OK, rem413*, wa-agree (general form of 4.13(b),(c)), til-bound.

Statements as proved:
- 4.13(b) `rem413b A B a oa e hA hB`, Omega_a = `omF a`, Omega_{a+1} = `omF (suc a)`.
- 4.13(c) `rem413c A B e`: no A c M(A).
- 4.13(d) `rem413d A : Seg (Cap (WA A) (om one)) OTc`.

Checker conventions learned: declare classes with full arity
(`WA (A : Cl) (y : T) : U wl = ...`), not `\ y -> ...`, or every `WA A y`
opens WA. Level name `wl` (lv, q, n, l, j taken by imports).

Open item x, y <' cat x y: done in Clos.seg (cat-lt-l, cat-lt-r).

Next: Def. 4.14, Remark 4.15, Lemma 4.16, 4.17 (closure).
