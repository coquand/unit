# Interface between workers A (`cca/`) and B (`em/`, `ccacoh/`)

Design: `CCA-DESIGN.md`.  Each worker edits only its own section below.  A
file listed as **stable** may be symlinked by the other worker; its
declarations listed here do not change name or type without a note here and
a message to the user.

## Worker A: provided

Stable (2026-10-24).  Link the files from `cca/` (and their imports, as in
`cca/All.seg`: `Prop214 Lemma216 StageInjective Prop235 LimFibre Lemma217
Lemma236 Prop237 PiClosure Prop239`, plus the link `AffineHLevels -> ../pn`).
All results are under `Over (ax : StoneAxioms[l,l].Assumptions)`.

| CCA | file | declaration | statement |
|---|---|---|---|
| Lemma 2.1.7 | `Lemma217` | `lemma217 S sS T sT inh : ||Approx[S, T]||` | `Approx[S,T]`: `Tk : Nat -> S -> U l`, `d k x : Tk (suc k) x -> Tk k x`, `finite k x : isFinite (Tk k x)`, `limit x : Equiv (T x) (DCh.Lim (\ k -> Tk k x) (\ k -> d k x))`, `sections k : ||(x : S) -> Tk k x||`; the stages are finite (Stone: `stage-stone`) |
| Prop. 2.3.5 | `Prop235` | `prop235 S sS Tw : isEquiv Colims[S,Tw].CP.colim Colims[S,Tw].Target Colims[S,Tw].canonical` | `Tower[S]`: `at : S -> Seq`, `sets i x : isSet ((at x).A i)` (sets suffice; overt discreteness is not used); `canonical [h] = x |-> [h x]`, `canonical-inc n h` its value on `CP.inc n h` |
| Prop. 2.3.7 (towers of finite sets) | `Prop237` | `prop237 E p fin I sI oI : isEquiv FMaps[E,p,I,sI].CF.colim (FMaps[E,p,I,sI].Lim -> I) FMaps[E,p,I,sI].canonical` | `FMaps` in `Lemma236`: `seq` = the sequence `E n -> I` (precomposition with `p`), `canonical [g] = g o pi_n`, `canonical-inc`; with a presentation: `Prop237[E,p,fin,I,sI,pr].equivalence` |
| Lemma 2.3.6 (towers of finite sets) | `Lemma236` | `Lemma236[E,p,fin,B,fB].equivalence`, `.injective`, `.surjective` | B finite |
| Prop. 2.3.9 | `Prop239` | `prop239 S sS I oI : isODisc ((x : S) -> I x)` | also `Lemma238[..].result`, `stone-fin-odisc`, `fin-pi-odisc`, small presentations `FinPres`, `fin-pres` |
| Lemma 2.1.6 | `Lemma216` | `lemma216 S sS V cover` | `V : Increasing[S]` (`sub`, `prop`, `mono`); openness not needed |
| Lemma 2.1.5, Prop. 2.1.4 (i), (ii), (iv), (v) | `Prop214` | `lemma215`, `finite-stone`, `fibre-stone`, `product-stone`, `local` (local choice for Stone spaces, record `Cover`), `bounded` | |

Added (2026-10-24, later; same rules), towers of **Stone** spaces:

| CCA | file | declaration | statement |
|---|---|---|---|
| Prop. 2.3.7 | `Prop237` | `prop237-stone E p sE I sI oI` (same conclusion as `prop237`, `sE : (n : Nat) -> isStone (E n)`); with a presentation `Scott237[E,p,sE,I,sI,pr].equivalence` | `prop237` (finite towers) is now an instance |
| Lemma 2.3.6 | `Lemma236Stone` | `lemma236-stone S p sS B fB`; `Stone236[..].injective`, `.surjective` | |
| Prop. 2.1.4 (iii) | `CountableProduct` | `lim-stone S p sS : isStone (DCh.Lim S p)`; also `pi-stone` (countable products), `NotAll` (not forall closed => some fails) | |
| — | `LimInhabited` | `lim-inhabited S p sS inh : ||DCh.Lim S p||` | a limit of inhabited Stone spaces is inhabited |
| Def. 2.3.10, Thm 2.3.11 | `Thm2311` | `thm2311 T : isEquiv Pis[T].PC.colim Pis[T].Target Pis[T].canonical` | `CTower`: `S`, `p`, `sS`, `I n : S n -> U l`, `q n x : I n (p n x) -> I (suc n) x`, `sI`, `oI`; `Pis[T].at y` is the sequence `I n (y n)` |

Imports, in order: `... Prop239 CountableProduct LimInhabited Lemma236Stone Prop237 Thm2311`
(see `cca/All.seg`).  So Lemma 3.1.5 can be stated for towers of Stone
spaces as in the paper.

Change (2026-10-24): `Thm2311.Pis` takes an `FTower` (`S p I q`, no
hypotheses); for a `CTower T` write `Pis[fam T]` (was `Pis[T]`).
`CTower` and `thm2311` are unchanged.

Added (2026-10-24), §2.4 and §3.4:

| CCA | file | declaration |
|---|---|---|
| Lemma 2.4.2, Prop. 2.4.3 | `Prop243` | `Lemma242[C, c, cC, cv]` (`S`, `p`, `down`, `square`, `lim-map`, `lim-onto`), `lim-chaus`, `Quot[..].chaus`, `local-chaus`, `sigma-chaus`, `id-chaus`, `finite-chaus` |
| Prop. 2.4.4, 2.4.5 | `Prop244`, `Prop245` | `tychonov I oI : PiCH I`, `prop245 C cC I oI` |
| Thm 2.4.6 | `Thm246` | `thm246 (T : HTower)` |
| the interval | `Interval` | `I`, `cs`, `cs-surjective`, `Rel`, `Over.chaus` |
| Lemma 3.4.1, Thm 3.4.3 (i) | `Lemma341` | `lemma341`, `thm343i` |
| Def. 3.4.2 | `Dyadic`, `Def342` | `Tuples k n`, `tuple-down`, `Def342[k].def342 : Equiv (Sigma x (Fin (k+1) -> Fibre cs x)) (lim Tuples k)` |
| Lemma C.0.5 | `LemmaC05` | `LemmaC05[Gr, n].AtOne[d, cocycle].trivial` (B's cocycle conventions) |
| Thm 3.4.3 (ii) | `Thm343ii` | `thm343ii Gr oG : CohZero I (\ x -> Gr)` |
| Lemma 3.4.4 (i), (ii) | `Lemma344` | `isLocal`, `odisc-local`, `bg-local` |

Added (2026-10-24, late), the ordered cochain complex, Lemma C.0.6 and
Ȟᵏ(I, T, A) = 0.  Link `cca/Cochains` (plain HoTT; needs only `pn/Torsor`,
`FinChoice`, `Truncation`); `LemmaC06`, `CechI` after `Thm343ii`.

| CCA | file | declaration | statement |
|---|---|---|---|
| ordered cochains | `Cochains` | `Cochains[Gr, Y]`: `Tup k = Fin k -> Y`, `C k = Tup k -> A`, `cons`, `tail`, `at k v phi` (= phi_v), `delta k : C k -> C (suc k)` | length k (degree k - 1; `C 0 = A`); `delta phi (v . t) = phi t - delta (phi_v) t`, so `delta phi (v, w) = phi w - phi v` (em/ImageGroup's convention) |
| | `Cochains` | `delta-sub`, `delta-delta`, `delta-cong`, `cone`, `Region[R, rR, sR].locality`; `Natural[Gr, Y, Y', f].natural` | additivity, delta delta = 0, cone, locality, naturality in the points |
| Def. 3.3.1 | `Cochains` | `Cech[X, Y, G]`: `Ch k = (x : X) -> C_(Y x) k`, `d`, `isCocycle k alpha`, `Bounds`, `Vanish k` | `Vanish k` = Ȟᵏ(X, Y, G) = 0 (alpha of length k + 1, beta of length k), merely |
| Lemma C.0.6 (and C.0.5, abelian) | `LemmaC06` | `LemmaC06[Gr, n].exact k : Exact All k` | the near-tuple complex on V n is exact at every length |
| Ȟᵏ(I, T, A) = 0 | `CechI` | `Over[ax].cech-I Gr oA k : Cech[In.I, Fibre In.cs, \ x -> Gr].Vanish k` | every k, A overtly discrete abelian |

Decision (user, 2026-10-24, late): A5 (Ȟ¹(I, T, B) = 0 for every
overtly discrete family B) is false (counterexample in
`HANDOFF-CCA-A.md`), so form (C) cannot give Thm 3.4.3 (iii).  Route
(C′): **wanted from B**, in `ccacoh/`, with the Čech complex of
`Cochains.Cech` (do not define another differential):
- the dimension shift in vanishing form: Ȟᵏ⁺¹(X, S, B) = 0 ⇒
  Ȟᵏ(X, S, L B) = 0 for any family B (L B = B^S / B as in `ImageGroup`);
- Thm 3.3.2 (C′): if `Vanish n` for all n >= 1 (for A), then
  Hⁿ(X, A) = 0 for all n >= 1.
With `cech-I` this gives Thm 3.4.3 (iii); A then does Lemma 3.4.4 (iii).

Added (2026-10-24, last): done with B's `Thm332C`.

| CCA | file | declaration | statement |
|---|---|---|---|
| Thm 3.4.3 (iii) | `Thm343iii` | `Over[ax].thm343iii Gr oA n : isConn 2 (In.I -> KK[Gr].K (suc n))` | H^(n+1)(I, A) = 0 |
| Lemma 3.4.4 (iii) | `Lemma344iii` | `Over[ax].em-local Gr oA m : Lemma344.isLocal (KK[Gr].K m)` | K(A, m) is I-local |
| — | `Lemma344` | `ByIds[Z, idl, onto].local` | identity types I-local and maps I -> Z merely constant give Z I-local |

Added (2026-10-24, after the join; same rules).  `Cochains` is unchanged
except for the module `AltSum` appended at its end.

| CCA | file | declaration | statement |
|---|---|---|---|
| Lemma 2.3.3 | `Lemma233` | `Over[ax].lemma233 X oX i y : OC.isOpen (InImage X i y)` | X a `Seq` of overtly discrete types, `InImage X i y = \|\|(z : X.A i) * inc i z = y\|\|`; for a `Prop235.Tower`, `Colims.Image phi i x` is `InImage (Tw.at x) i (phi x)` |
| Lemma 2.3.4 | `Lemma233` | `Over[ax].lemma234 S sS Tw w : \|\|Fibre Images[S,Tw].map w\|\|` | `Images[S,Tw]`: `Im i x` (image of stage i in colim I x, a subset), `ims` the tower of `(x : S) -> Im i x`, `map : colim_i ((x : S) -> I i x) -> colim ims` (induced by the stage maps); also `forget` (injective) and `forget-map : forget (map u) = canonical u` |
| Def. 3.3.1 (the sum) | `Cochains` | `AltSum[Gr, Y].alt-delta k phi s : delta k phi s = alt k phi s` | `alt k phi s = sum_{i : Fin (k+1)} sign (index i) (phi (omit k i s))`, i.e. the paper's alternating sum; `omit`, `sum`, `sign`, `index`, `sum-inv` |

## Worker B: provided

Stable (2026-10-24): K(A, n).  Link the files of `em/` in the order of
`em/All.seg` (`NatArith HLevels Connected EquivProp Lemma4 FundThm TruncUp
PtEquivOps Completion Deloop Retracts DeloopMaps Whitehead EM`; links to
`pn/` and `replacement/Completion` as there).  Plain HoTT: no
`StoneAxioms`.  Levels: `isTrunc n X` = X is (n-2)-truncated,
`isConn n X` = X is (n-2)-connected (`HLevels`, `Connected`).

| what | declaration (in `EM.EMSpace[Gr]`, `Gr : Torsor.Ab`) | type |
|---|---|---|
| K(A, n+1) | `K n` | `U l` (small) |
| base point | `pt n` | `K n` |
| n-connected | `conn n` | `isConn (suc (suc n)) (K n)` |
| (n+1)-truncated | `trunc n` | `isTrunc (suc (suc (suc n))) (K n)` |
| Ω K(A, n+2) ≃pt K(A, n+1) | `loops n` | `PtEquiv (Id (K (suc n)) (pt (suc n)) (pt (suc n))) (refl (pt (suc n))) (K n) (pt n)` |
| Ω K(A, 1) ≃ A, a group isomorphism | `loop0`, `loop0-hom` | `Equiv (Id (K zero) (pt zero) (pt zero)) A` |
| identity types of K(A, n+2) are merely K(A, n+1) | `paths n x y` | `Trunc[Equiv (Id (K (suc n)) x y) (K n)]` |
| identity types of K(A, 1) are merely A | `paths0 x y` | `Trunc[Equiv (Id (K zero) x y) A]` |

`PtEquiv A a0 B b0 = (f : PtMap A a0 B b0) * isEquiv A B f.1`,
`PtMap A a0 B b0 = (f : A -> B) * Id B (f a0) b0` (`Lemma4`); accessors in
`PtEquivOps.Acc`.  K(A, 0) = A is not a separate declaration.

Stable (2026-10-24): non-abelian H¹, CCA §3.1 in the vanishing form.
Link `em/Group`, `em/GTorsor`, `em/CechNA` (plain HoTT; they need
`stoneseq/CechComplex`) and `ccacoh/ScottCech`, `ccacoh/H1Stone` (after
your `cca/` files up to `Prop237`).

| CCA | file | declaration | statement |
|---|---|---|---|
| groups | `Group` | `Grp` (record: `G setG e mul inv assoc unitl unitr invl invr`), `ab-grp : Torsor.Ab -> Grp` | |
| BG = G-torsors (Def. A.0.3) | `GTorsor` | `GTor[Gr].Tor : U l+`, `triv`, `pt-triv X p : triv = X`, `triv-pt`, `decode` | LEFT action, pn's layout: for `ab-grp A` it is `TorId[A].Tor` by definition |
| H¹(X, G) = 0 | `CechNA` | `CohZero X G` | every `alpha : (x : X) -> GTor[G x].Tor` is merely `triv` pointwise |
| Ȟ¹(X, Y, G) = 0 (Def. 3.1.1, 3.1.2) | `CechNA` | `CechNA[X, Y, hY, G].H1Zero` | cocycle `d y1 y2 . d y0 y1 = d y0 y2`; trivial: merely `g` with `g y1 . d y0 y1 = g y0` (CCA's formulas mirrored, left torsors) |
| Lemma A.0.1 | `CechNA` | `CechNA[..].lemmaA01 t` | a section of Y gives Ȟ¹ = 0 |
| Cor. A.0.8 (vanishing) | `CechNA` | `CorA08[X, Y, hY, G].forward : CohZero X G -> H1Zero`, `.backward : CohZero ((x : X) * Y x) (G o pr1) -> H1Zero -> CohZero X G` | |
| Lemma 3.1.6 | `H1Stone` | `Over[ax].lemma316 S sS T sT inh G oG : CechNA[S, T, inh, G].H1Zero` | `oG : (x : S) -> isODisc (G x).G` |
| Prop. 3.1.7 | `H1Stone` | `Over[ax].prop317 S sS G oG : CohZero S G` | |
| Prop. 3.1.8 (vanishing) | `H1Stone` | `Over[ax].Prop318[X, S, sS, q, onto, G, oG].forward`, `.backward` | `q : S -> X`, `onto : DCh.Surjective q`; fibres `Bijection.Fibre q x`; X any type (compact Hausdorff not used): H¹(X, G) = 0 iff Ȟ¹(X, S, G) = 0 |

Stable (2026-10-24): fibre sequences, ε and §3.2.  Link from `em/` (plain
HoTT) `LoopCalc Fibres EMMaps Bijection PiEquiv FibSeq Exact Eps ImageGroup`
(after `EM`), and `ccacoh/Thm325` (after `H1Stone`; `ccacoh/All.seg` has the
order).  Uniform indexing `EMMaps.KK[Gr]`: `K m` = K(A, m) with `K 0` the
group, `pt m`, `e m : PtEquiv (Omega K(A, m+1)) K(A, m)`, `conn m`, `trunc m`.

| CCA / DW1 | file | declaration | statement |
|---|---|---|---|
| K(h, m) for h : A -> B | `EMMaps` | `KMap[Ga, Gb, h].K m`, `loopK m` | pointed; loop (K h (m+1)) = e ; K h m ; e^-1 |
| fibre sequence of 0 -> A -> B -> C -> 0 | `FibSeq` | `SES[Ga, Gb, Gc, i, p, inj, pi0, ex, sur].fibre m` | `z |-> (K i m z, h z)` : K(A, m) ~ Fib (K p m) |
| exactness H^m(S,C) -> H^(m+1)(S,A) -> H^(m+1)(S,B) | `Exact` | `Exact[S, A, B, C, i, p, inj, pi0, ex, sur, m].exact cC alpha z` | 0-connected form: Pi K(C x, m) 0-connected and K i o alpha merely trivial give alpha merely trivial |
| Def. 3.2.1 (ε) | `Eps` | `Eps[S, A].eps m`, `loop-eps m` | defined by delooping |
| Lemmas 3.2.2, 3.2.3, 3.2.4 | `Eps` | `Eps[S, A].vanish m eq`, `Emb[m, eq].emb`, `Emb[m, eq].equiv c` | |
| L = A^T / A | `ImageGroup` | `Cech[T, hT, Ga].L`, `i`, `p`, `inj`, `pi0`, `ex`, `sur` | the image of the Čech differential (no quotient); overtly discrete: `Thm325.Over[ax].odiscL` |
| Thm 3.2.5 | `Thm325` | `Over[ax].thm325 m S sS A oA : isEquiv (eps m).1` | S Stone, `oA : (x : S) -> isODisc (A x).A` |
| Cor. 3.2.6 | `Thm325` | `Over[ax].cor326 m S sS A oA : isConn 2 ((x : S) -> K(A x, m+1))` | H^(m+1)(S, A) = 0 |

Stable (2026-10-24): Thm 3.3.2 in the form (C) chosen by the user
(`CCA-DESIGN.md` §5).  Link `ccacoh/Thm332` (after `Thm325`).

| CCA | declaration (in `Thm332.Over[ax, X, sX, idc, S, sS, q, onto]`) | statement |
|---|---|---|
| — | `sX : isSet X`, `idc : (x y : X) -> isClosed (Id X x y)` (X compact Hausdorff), `q : S -> X` onto, S Stone | fibres `Sx x = Bijection.Fibre q x`, Stone: `sSx` |
| hypothesis | `Hyp` | for every `B : X -> Ab` with `oB : (x : X) -> isODisc (B x).A`: `CechNA[X, Sx, onto, ab-grp o B].H1Zero` |
| from the abelian Čech complex | `abelian B z` | `stoneseq/CechComplex.Cech[X, Sx, B].H1Zero` gives the hypothesis for B |
| Thm 3.3.2 (C) | `thm332 hyp n B oB : isConn 2 ((x : X) -> KK[B x].K (suc n))` | H^(n+1)(X, B) = 0 for all n |
| S is a Čech cover (Def. B.0.3) | `Cov[B, oB, n].conn` | H^(n+1)(X, B^S) = 0 |

For Thm 3.4.3 (iii): with Ȟ¹(I, T, B) = 0 for all overtly discrete B (the
computation of (ii)) this gives Hⁿ(I, A) = 0 for n >= 1; Lemma C.0.6 is
not needed.  Not done (decision §5): Appendix B on the Čech side, the
group isomorphism, Cor. A.0.7 / Prop. 3.1.8 as bijections of sets.

Stable (2026-10-24): the degree-1 comparison as bijections of sets.
Link `em/CorA07` (after `ImageGroup`; needs `Quotient`, `Bijection`,
`Equivalences`) and `ccacoh/Prop318Set` (after `H1Stone`).

| CCA | file | declaration | statement |
|---|---|---|---|
| Ȟ¹(X, Y, G), H¹(X, G), H¹(X, Y, G) as sets | `CorA07` | `CorA07[X, Y, hY, G].Cech`, `.H1`, `.H1Y : U l+` | quotients of `Cyc` by `Coh`, of `Fam` and of pointed families by mere equality |
| Prop. 3.1.4 = Cor. A.0.7 | `CorA07` | `CorA07[..].corA07 : Equiv Cech H1Y` | map induced by Ψ (`psibar`) |
| Cor. A.0.8 | `CorA07` | `CorA07[..].A08[hyp].corA08 : Equiv Cech H1` | `hyp : CohZero ((x : X) * Y x) (\ w -> G w.1)` |
| Prop. 3.1.8 | `Prop318Set` | `Over[ax, X, S, sS, q, onto, G, oG].prop318 : Equiv A7.Cech A7.H1` | fibres `Bijection.Fibre q x`, X any type |

Stable (2026-10-24): Thm 3.3.2 in the form (C') (`CCA-DESIGN.md` §5),
on A's `cca/Cochains` (linked read-only from `em/`).  Link `em/FibreTorsor`,
`em/Cochains` (= A's), `em/CechHigher` (after `CorA07`), and
`ccacoh/LiftStone`, `ccacoh/Thm332C` (after `Thm332`; `ccacoh/All.seg`
has the order).  `Thm332.Over.Step` now takes the connectivity of L as an
argument (`Step[n, B, oB, cL]`); `thm332` (form (C)) is unchanged.

| CCA | file | declaration | statement |
|---|---|---|---|
| — | `CechHigher` | `Natural[Y, Ga, Gb, h].natural` | `delta (h o phi) = h o delta phi` for a homomorphism h |
| Ȟ¹ forms agree | `CechHigher` | `H1Bridge[X, Y, hY, B].h1zero : Cochains.Cech[X, Y, B].Vanish (suc zero) -> CechNA[..].H1Zero` | |
| dimension shift | `CechHigher` | `Shift[X, Y, hY, B].vanishS n : Cochains.Cech[X, Y, B^Y].Vanish (suc n)`, `.shift n lifts : Vanish_B (suc (suc n)) -> Vanish_L (suc n)` | L = `ImageGroup.Cech.L`; `lifts` = part (2) |
| lifting over Stone | `LiftStone` | `Over[ax, W, sW, ..].lift` | sections of C lift along p over a Stone W (A overtly discrete) |
| Thm 3.3.2 (C') | `Thm332C` | `Over[ax, X, sX, idc, S, sS, q, onto].thm332 n B oB v : isConn 2 ((x : X) -> KK[B x].K (suc n))` | `v : AllVanish B = (m : Nat) -> Cochains.Cech[X, Sx, B].Vanish (suc m)` (A's Čech complex and indexing: Ȟ^(m+1) = 0) |
| | `Thm332C` | `w-stone k : isStone ((x : X) * (Fin (k+1) -> Sx x))` | |

Revised (2026-10-24, same day): B's own Čech complex is gone (one name per
notion); everything is stated with A's `Cochains.Cech` (`Ch`, `d`,
`isCocycle`, `Bounds`, `Vanish k` = Ȟ^k = 0).  For Thm 3.4.3 (iii): pass
`\ m -> cech-I (suc m)` (type `Cochains.Cech[I, Fibre cs, \ x -> Gr].Vanish (suc m)`)
as `v` to `Thm332C.Over.thm332`.

Added by worker A in B's directories (2026-10-24, B on other work; same
rules).  `ScottCech.Stages` keeps its names (now an instance of
`ScottCech.Tower`, a tower of Stone spaces).

| CCA | file | declaration | statement |
|---|---|---|---|
| Lemma B.0.1 | `em/CechZero` | `CechZero[X, Y, hY, A].lemmaB01 : Equiv H0 Z0` | `H0 = (x : X) -> (A x).A`, `Z0` the 0-cocycles of `Cochains.Cech`; additive, natural in A (`Natural0.natural`) |
| — | `em/CechPull` | `Pull[X, Y, Y', hY, hY', G, f].map`, `.injective` | restriction of Ȟ¹ classes along `f x : Y' x -> Y x`; injective |
| Lemma 3.1.5 | `ccacoh/Lemma315` | `Over[ax].Lemma315[S, sS, Tk, dk, sT, inh, G, oG].equivalence : Equiv CH.colim AL.Cech` | colim_k Ȟ¹(S, T k, G) = Ȟ¹(S, lim T, G) |
| Cor. A.0.7, A.0.8 (pointed) | `em/CorA07Pt` | `CorA07Pt[X, Y, hY, G].corA07-pointed`, `corA08-pointed hyp` | base points `base-cech`, `base-h1y`, `base-h1` |
| Prop. 3.1.8 (pointed) | `ccacoh/Prop318Set` | `Over[..].prop318-pointed` | |
| Def. 3.2.1 | `em/EpsEv` | `EpsEv[S, A].claim m x`, `eps-ev m z x : (eps m).1 z x = (KMap[PA, A x, ev x].K m).1 z` | ε is the canonical map |

Added by worker A (2026-10-24): CCA Thm 3.3.2 as stated.  Link from em/
(plain HoTT, in this order after EpsEv): `QGrp PiOne Puppe LoopConj PiPt LES
CechGroups Snake CechLES Coker KFun CechNat CechH0 ImageMap LiftUnique FibMap
EH LESNat`, then `ccacoh/Thm332A`.

| CCA | file | declaration | statement |
|---|---|---|---|
| Thm 3.3.2 | `ccacoh/Thm332A` | `Over[ax, X, sX, idc, S, sS, q, onto].thm332-iso n : Stage n` | `Stage n = (Phi : (B : X -> Ab) -> ODF B -> Iso n B) * Natural n Phi`; `Iso n B`: a group homomorphism `HG[n, B].P.grp -> CH[n, B].C.H[n].Q.QG.grp`, injective and onto; `Natural`: commutes with `HM` (π₁ of the products of K(h)) and `CM` (h_* on Ȟⁿ) |
| Hⁿ(X, B) | `em/PiOne`, `em/Eps` | `PiOne[Eps[X, B].P (suc n), Eps[X, B].pP (suc n)].grp` | π₁ of (x : X) -> K(B x, n+1) |
| Ȟⁿ(X, Y, B) | `em/CechGroups` | `CechGrp[X, Y, B].H[n].Q.QG.grp` | cocycles modulo coboundaries (Ȟ⁰ = Z⁰) on `cca/Cochains` |
| Lemma B.0.4 | `em/LES`, `em/LESNat` | `LES[..., n].delta`, `delta-onto cE`, `delta-pstar`, `ker-im`; `LESNat[...].natural` | exact, δ natural |
| Lemmas B.0.5-B.0.7 | `em/CechLES`, `em/CechNat` | `CechLES[..., lifts, n].delta`, `Onto[vanB].onto`, `delta-pstar`, `ker-im`; `CechNat[...].natural` | |

