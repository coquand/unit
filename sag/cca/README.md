# cca: Cohomology in synthetic Stone duality, worker A

CCA.pdf (Cherubini–Coquand–Geerligs–Moeneclaey).  Design:
`../CCA-DESIGN.md`; interface with worker B: `../CCA-INTERFACE.md`; gaps
and notes: `../HANDOFF-CCA-A.md`.  Check with `./segc sag/cca changed` from
the `unit` root.  Everything is under `Over (ax : StoneAxioms[l,l].Assumptions)`.

## Proved (CCA numbering)

| CCA | statement | file, declaration |
|---|---|---|
| Prop. 2.1.4 (i) | finite sets are Stone | `Prop214.finite-stone` |
| Prop. 2.1.4 (ii) | fibres, binary products (with SSD Thm 4.18) | `Prop214.fibre-stone`, `product-stone` |
| Prop. 2.1.4 (iii) | sequential limits (and countable products) of Stone spaces are Stone | `CountableProduct.lim-stone`, `pi-stone` |
| Prop. 2.1.4 (iv) | local choice for Stone spaces | `Prop214.local` (record `Cover`) |
| Prop. 2.1.4 (v) | maps S -> N are bounded | `Prop214.bounded` |
| Lemma 2.1.5 | forall over a Stone space of open propositions is open | `Prop214.lemma215` |
| Lemma 2.1.6 | an increasing cover of a Stone space is eventually everything | `Lemma216.lemma216` |
| Lemma 2.1.7 | towers of finite families approximating T, with sections | `Lemma217.lemma217` (record `Approx`) |
| — | a limit of inhabited Stone spaces is inhabited | `LimInhabited.lim-inhabited` |
| Lemma 2.3.4 | (form used by 2.3.5) | `Prop235.Prop235.Lemma234` |
| Prop. 2.3.5 | colim_i Pi_x I_i x = Pi_x colim_i I_i x | `Prop235.prop235` |
| Lemma 2.3.6 | colim_k (S_k -> F) = (lim S -> F), F finite | `Lemma236Stone.lemma236-stone` (finite towers: `Lemma236`) |
| Prop. 2.3.7 | colim_k (S_k -> I) = (lim S -> I), I overtly discrete | `Prop237.prop237-stone` (finite towers: `prop237`) |
| Lemma 2.3.8 | descent of overt discreteness along a surjection | `Prop239.Lemma238` |
| Prop. 2.3.9 | Tychonov's dual: Pi_{x : S} I x overtly discrete | `Prop239.prop239` |
| Def. 2.3.10, Thm 2.3.11 | Scott continuity for towers in C_Stone | `Thm2311.CTower`, `thm2311` |

| §3.4 (interval) | I = 2^N / ~, ~ the closed relation of the dyadic numerators; I compact Hausdorff | `Interval.I`, `cs`, `Rel`, `Over.chaus` |
| Lemma 3.4.1 | maps from I to a finite set are constant | `Lemma341.lemma341` |
| Thm 3.4.3 (i) | maps from I to an overtly discrete type are constant | `Lemma341.thm343i` |
| Def. 3.4.2 | I~^k_n (tuples of near vertices, finite), and Sigma_x (cs^-1 x)^(k+1) = lim_n I~^k_n | `Dyadic.Tuples`, `TupleFinite.finite`, `tuple-down`; `Def342.Def342[k].def342` |
| Lemma C.0.5 | exactness at G, G^(I~^0), G^(I~^1) | `LemmaC05.LemmaC05[Gr, n].at-G`, `AtZero.constant`, `AtOne.trivial` |

| Lemma 2.4.2 | Stone covers of a tower of compact Hausdorff spaces, onto on the limit | `Prop243.Lemma242` |
| Prop. 2.4.3 (i)-(v) | compact Hausdorff: finite, Id, Sigma, quotients by closed equivalence relations, sequential limits, local choice | `Prop243.finite-chaus`, `id-chaus`, `sigma-chaus`, `Quot.chaus`, `lim-chaus`, `local-chaus` |
| Prop. 2.4.4 | Tychonov | `Prop244.tychonov` |
| Prop. 2.4.5 | Tychonov's dual for compact Hausdorff spaces | `Prop245.prop245` |
| Thm 2.4.6 | Scott continuity for towers in C_CHaus | `Thm246.HTower`, `thm246` |
| Thm 3.4.3 (ii) | H^1(I, G) = 0, G overtly discrete | `Thm343ii.thm343ii` |
| Lemma 3.4.4 (i), (ii) | overtly discrete types and BG are I-local | `Lemma344.odisc-local`, `bg-local` |
| Def. 3.3.1, C.0.4 | ordered cochains, delta (recursion on the first point), additivity, delta delta = 0, cone, locality, naturality; the Čech complex and its vanishing | `Cochains.Cochains`, `Natural`, `Cech` |
| Lemma C.0.6 (C.0.5 for abelian G) | the near-tuple complex on V n is exact at every length | `LemmaC06.LemmaC06[Gr, n].exact` |
| — | Ȟᵏ(I, cs^-1, A) = 0 for every k, A overtly discrete abelian | `CechI.Over.cech-I` |
| Thm 3.4.3 (iii) | H^(n+1)(I, A) = 0, A overtly discrete abelian | `Thm343iii.Over.thm343iii` (B's Thm 3.3.2 (C′) + `cech-I`) |
| Lemma 3.4.4 (iii) | K(A, m) is I-local | `Lemma344iii.Over.em-local`; the general step `Lemma344.ByIds` (identity types local + maps merely constant) |

Supporting files: `StageInjective` (injective on one stage), `LimFibre`
(fibres commute with limits), `PiClosure` (finite products of finite and
overtly discrete types, Pi along fibres, finite => overtly discrete),
`Prop239.FinPres` (small presentations).

`Dyadic` (vertices V n = numerators below 2^n, 2^N = lim V),
`Group` (link to worker B's `em/Group`).

Worker B's stable files are linked (read-only): `em/Group`, `GTorsor`,
`CechNA`, `PiEquiv`, `FundThm`, `ccacoh/ScottCech`, `H1Stone`.

All of §3.4 in scope is done (Prop. 3.4.5 is out of scope).  Worker B's
files of `em/` and `ccacoh/` up to `Thm332C` are linked read-only.
