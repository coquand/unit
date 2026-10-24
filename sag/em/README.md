# em: Eilenberg–MacLane spaces in plain HoTT

Worker B of the CCA formalisation (`../CCA-DESIGN.md`, `../HANDOFF-CCA-B.md`).
Wärn, *Eilenberg–MacLane spaces and stabilisation in HoTT* (`DW1.pdf`),
§2, §3, §4.1, and what CCA uses of them.  No SSD axioms: only univalence,
function extensionality and replacement (the `Theory` parameters).  Check
with `./segc sag/em changed` from the `unit` root.

Levels are indexed by `Base.Nat` with offset 2 (DW1 footnote 2, recursive):
`isTrunc n X` is "X is (n-2)-truncated" (`isTrunc 0` = contractible),
`isConn n X` is "X is (n-2)-connected" (`isConn 0` = `Top`).

## Proved (DW1 numbering)

| DW1 | statement | file, declaration |
|---|---|---|
| fn. 2 | truncation and connectedness levels, closure under retracts, Π, Σ, cumulativity, being a level is a proposition | `HLevels`, `Connected` |
| Lemma 4 | pointed sections over a (c-1)-connected base with (c+t-2)-truncated fibres are (t-2)-truncated | `Lemma4.lemma4` |
| Cor. 5 | (i) pointed maps, (ii) pointed equivalences (for m ≥ -1) | `Lemma4.cor5-map`, `cor5-equiv` |
| Def. 1 | X-torsors T X, small (Y ranges over the image BAut X of the point X in U) | `Deloop.Torsors.Tor` |
| Lemma 3 | pointed torsors and pointed sections of x ↦ X ≃pt (X, x): levels pass (retract form) | `Deloop.Torsors.lemma3` |
| Cor. 6, 7, 8 | levels of pointed torsors; contractible (2n-truncated X); contractible if T X merely inhabited ((2n+1)-truncated X) | `Deloop.Torsors.cor6`, `cor7`, `cor8` |
| Thm. 2 | existence: if pointed torsors are contractible, Ω(T X, pt) ≃pt X; T X is (n+1)-connected and (k+1)-truncated if X is n-connected and k-truncated | `Deloop.Torsors.Deloop.theorem2`, `tor-conn`, `tor-trunc` |
| Lemma 9 | Ω⁻¹ f is a retract of (a : A) → (b : B) × C a b | `DeloopMaps.Maps.Over.lemma9` |
| Cor. 10 | Ω⁻¹ f is m-truncated (A n-connected, B (2n+m+2)-truncated) | `DeloopMaps.Maps.Over.Levels.cor10` |
| Cor. 11 | Ω⁻¹ f contractible for B 2n-truncated | `DeloopMaps.Maps.Over.cor11` |
| Cor. 12 | n = 0: a multiplicative f has a unique delooping | `DeloopMaps.Maps.Over.Mult.cor12` |
| §4.1 | K(A, n) for A abelian and all n ≥ 1, n-1-connected, n-truncated, Ω K(A, n+1) ≃pt K(A, n), Ω K(A, 1) ≃ A as groups; identity types of K(A, n+1) merely K(A, n) | `EM.EMSpace` (`K n` = K(A, n+1)) |
| §4.1 | deloopings of homomorphisms K(h, m), with loop (K h (m+1)) = e ; K h m ; e⁻¹ | `EMMaps.KMap.K`, `loopK` |
| — | the fibre sequence K(A, m) ≃ Fib (K p m) of a short exact sequence 0 → A → B → C → 0, for all m | `FibSeq.SES.fibre` |
| — | exactness Hᵐ(S, C) → Hᵐ⁺¹(S, A) → Hᵐ⁺¹(S, B) (0-connected form) | `Exact.Exact.exact` |
| CCA Def. 3.2.1, Lemmas 3.2.2–3.2.4 | ε : K(Π A, m) → Π K(A x, m) and its properties | `Eps.Eps.eps`, `vanish`, `Emb.emb`, `Emb.equiv` |
| — | ε_T ∘ K(diagonal) = diagonal (constant family over T) | `Eps.Diag.claim` |
| CCA §3.2 | L = A^T/A as the image of the Čech differential, with its short exact sequence | `ImageGroup.Cech` |
| CCA App. A | non-abelian G-torsors, Čech H¹, Lemmas A.0.1, A.0.2 (i), A.0.4, A.0.6 and Cor. A.0.8 (vanishing form) | `Group`, `GTorsor`, `CechNA` |
| CCA Prop. 3.1.4 = Cor. A.0.7, Cor. A.0.8 | as bijections of sets: Ȟ¹(X, Y, G) ≃ H¹(X, Y, G), and ≃ H¹(X, G) when H¹(Σ Y, G ∘ π) = 0; with Lemmas A.0.2 (ii), A.0.4 (iii), A.0.5, A.0.6.  Sets by `Quotient` (replacement); H¹(X, Y, G) is the quotient of the pointed families, a subset of H¹(X, G) (`forget-injective`) | `CorA07`: `CorA07.corA07`, `CorA07.A08.corA08` |
| CCA Def. 3.3.1 (vanishing form), Čech dimension shift | Ȟ^k = 0 is worker A's `Cochains.Cech.Vanish k` (linked); naturality of δ; Ȟ(B^Y) = 0 (cone); the shift to L = B^Y / B given lifts; Ȟ¹ forms agree with `CechNA` | `CechHigher` |
| — | the fibre of p over c in 0 -> A -> B -> C -> 0 is an A-torsor | `FibreTorsor` |
| CCA Lemma B.0.1 | Ȟ⁰(X, Y, A) = H⁰(X, A) = (x : X) -> A x for Y x merely inhabited; additive, natural in A | `CechZero`: `CechZero.lemmaB01`, `Natural0.natural` |
| — | restriction of Ȟ¹ classes along a map of covers Y' x -> Y x; it commutes with Ψ, so it is injective | `CechPull`: `Pull.map`, `Pull.psi-pull`, `Pull.injective` |
| CCA Prop. 3.1.4 = Cor. A.0.7, Cor. A.0.8 | as isomorphisms of pointed sets: the unit cocycle goes to the trivial family (psi of the unit cocycle is the trivial torsor) | `CorA07Pt`: `corA07-pointed`, `corA08-pointed` |
| CCA Def. 3.2.1 | eps m is the canonical map: ev_x o eps m = K(ev_x, m) as pointed maps, so eps m z x = K(ev_x, m) z | `EpsEv`: `EpsEv.claim`, `eps-ev` |
| — | groups: quotients by a congruence (`QGrp`), π₁ and π₁ of pointed maps (`PiOne`), kernels, quotients by subgroups (`CechGroups.Kern`, `QAb`), isomorphic cokernels (`Coker`) | |
| — | Puppe sequence, exactness of looped fibre sequences, maps of fibres along pointed squares, unique lifts, conjugation of loopings, Eckmann-Hilton | `Puppe`, `FibMap`, `LiftUnique`, `LoopConj`, `EH` |
| — | products of pointed maps, their fibres and loopings; K(-, m) is a functor | `PiPt`, `KFun` |
| CCA Lemma B.0.4 | the long exact sequence Hⁿ(E) -> Hⁿ(L) -> Hⁿ⁺¹(A) -> 0 of groups, natural | `LES`, `LESNat` |
| CCA Lemmas B.0.5-B.0.7 | the Čech long exact sequence in the degrees used, natural; Ȟᵏ as groups | `CechGroups`, `Snake`, `CechLES`, `CechNat`, `ImageMap` |
| CCA Thm 3.3.2, n = 0 | H⁰ = Ȟ⁰ as groups, naturally | `CechH0` |

Supporting results: the fundamental theorem of identity types (`FundThm`),
being an equivalence is a proposition (`EquivProp`), pointed equivalences,
their induction principle and pointed univalence (`PtEquivOps`), retracts
as a record with composition, Σ of retracts and Σ over an equivalence of
bases (`Retracts`), paths of pointed maps (`DeloopMaps.ptmap-path`),
Whitehead's principle for 0-connected types (`Whitehead.Pointed`);
pointed composition, its laws and the functoriality of looping, maps
determined by their loopings (`LoopCalc`); fibres: Ω Fib f ≃ Fib (loop f),
fibres along squares of pointed equivalences, 0-connectedness, lifting a
null map (`Fibres`).

## How K(A, n) is built

- K(A, 1) = the small A-torsors `pn/TrivialGerbe.TrivG.K`, with its band.
- K(A, 2) = T K(A, 1) by Cor. 8 (n = 0).  T K(A, 1) is merely inhabited
  by a homogeneous structure μ x : K(A,1) ≃pt (K(A,1), x): the group
  isomorphism band_x⁻¹ ∘ band_0 deloops by Cor. 12 and the delooping is an
  equivalence by Whitehead.  (DW1 argues through the centre Z(A); this is
  the same in substance, written directly.)
- K(A, n+3) = T K(A, n+2) by Cor. 7, by recursion on n (`EM.Kstage`, a
  `Stage` record holding the type, point, connectivity and truncation).
