# Worker B: Eilenberg–MacLane spaces (DW1.pdf) and cohomology (CCA.pdf)

Read first: `sag/CCA-DESIGN.md` (scope, split, representation choices, rules),
`sag/CCA-INTERFACE.md`, `DW1.pdf` (§2, §3, §4.1), `CCA.pdf` §3.1–3.3 and
Appendices A, B, and `stoneseq/README.md` for what SSD §5 already gives.
You own `sag/em/` (plain HoTT, no SSD axioms) and `sag/ccacoh/`.  Worker A works in
`sag/cca/` at the same time.  Do not commit.

## Steps

- **B0. Skeleton.** `em/All.seg` (foundation from `pn/`, with `Torsor`,
  `TorsorId`, `Gerbe`) and `ccacoh/All.seg` (also `stoneseq/`, `stone/`, and
  A's `cca/` files once announced).  Check: `./segc sag/em changed` from the `unit` root.
- **B1. `em/`: DW1 §2–§3** (plain HoTT).
  - Truncation and connectedness levels (DW1 footnote 2, recursive), with
    the basic closure facts.
  - Lemma 4 (pointed sections over an n-connected base are m-truncated), by
    induction on n; Cor. 5, 6.
  - T X (Def. 1, small by replacement as in `pn/Torsor.seg`), Lemma 3,
    Thm 2 (existence half only), Cor. 7, 8.
  - Lemma 9, Cor. 10, 11, 12 (deloopings of maps).
- **B2. `em/`: K(A, n)** (DW1 §4.1).  K(A, 1) = torsors (relate to
  `pn/Torsor`), K(A, 2) by Cor. 8 (A abelian: the section of Z(A) -> A),
  K(A, n+1) = T(K(A, n)) by Cor. 7, by recursion on n.  Then what CCA §3.2
  uses: the map ε : K(Π x. A x, n) -> Π x. K(A x, n) (CCA Def. 3.2.1) and
  Lemmas 3.2.2–3.2.4; for a short exact sequence 0 -> A -> B -> C -> 0 the
  fibre sequence K(A, n) -> K(B, n) -> K(C, n) and the exactness
  Hⁿ(X, C) -> Hⁿ⁺¹(X, A) -> Hⁿ⁺¹(X, B) in the "0-connected" form of
  `CCA-DESIGN.md` §4.  Announce K(A, n) and these as stable (A needs
  K(A, n) for Lemma 3.4.4 (iii)).
- **B3. `em/`: Appendix A** (H¹(X, Y, G) = Ȟ¹(X, Y, G) for non-abelian G,
  Cor. A.0.7, A.0.8) and **Appendix B** (Lemmas B.0.1, B.0.2, B.0.4–B.0.6;
  B.0.6 cites a missing B.0.7: supply it).  Your `stoneseq/CechComplex`
  (Lemmas 5.5–5.7) is the abelian degree-1 case: generalise, do not copy.
- **B4. `ccacoh/` (after A's Props 2.3.5, 2.3.7, 2.3.9 and Lemma 2.1.7):**
  §3.1 (Lemma 3.1.5, Lemma 3.1.6, Prop. 3.1.7: H¹(S, G) = 0 for S Stone and
  G a family of overtly discrete groups; Prop. 3.1.8), generalising your
  `Lemma510`; §3.2 (Thm 3.2.5, Cor. 3.2.6: Hⁿ(S, A) = 0).  Announce
  Prop. 3.1.8 as stable (A needs it for Thm 3.4.3 (ii)).
- **B5. §3.3, Thm 3.3.2.** First write in `CCA-DESIGN.md` §5 which form is
  feasible (full group isomorphism, or the vanishing form) and ask the user
  before starting.

Done when each step checks under `./segc sag/em changed` / `./segc sag/ccacoh
changed`, every file < 10 s, and `em/README.md`, `ccacoh/README.md` list
what is proved with DW1 / CCA numbering.

## Progress (2026-10-24)

- B0 done: `em/All.seg` (pn foundation + `replacement/Completion`),
  `ccacoh/All.seg` (all of `stoneseq/`, `stone/` by links).
- B1 done: DW1 §2, §3 in `em/` (see `em/README.md`); B2 so far: K(A, n)
  for all n (`EM.EMSpace`), announced stable in `CCA-INTERFACE.md`.
- Every `em/` file checks in < 0.02 s.  `--opened` (rule 6): no declaration
  above 30 distinct definitions opened (largest: `EM.EM1.band-unband` 29,
  `DeloopMaps.Maps.Over.Levels.cell0` 19).
- B3 (part) and B4 (part) done, out of order because worker A needs
  Prop. 3.1.8 for Thm 3.4.3 (ii): non-abelian torsors and Čech H¹
  (`em/Group`, `em/GTorsor`, `em/CechNA`: Lemmas A.0.1, A.0.2 (i), A.0.4,
  A.0.6 and Cor. A.0.8 in the vanishing form), and `ccacoh/ScottCech`,
  `ccacoh/H1Stone`: Lemma 3.1.5 (form used), 3.1.6, Prop. 3.1.7,
  Prop. 3.1.8 (vanishing form); announced in `CCA-INTERFACE.md`.
  Largest `--opened`: `ScottCech...phi2-inc` 26.
- B2 done: K(h, m) (`em/EMMaps`), the fibre sequence of a short exact
  sequence for all m (`em/FibSeq`), exactness in the 0-connected form
  (`em/Exact`), ε and Lemmas 3.2.2–3.2.4 (`em/Eps`), the cokernel as an
  image (`em/ImageGroup`).  B4 §3.2 done: Thm 3.2.5, Cor. 3.2.6
  (`ccacoh/Thm325`).  All announced in `CCA-INTERFACE.md`.  Full checks:
  em 0.07 s, ccacoh 1.5 s (141 modules); largest `--opened` 57
  (`Eps.Diag.DStep.chain`).
- B5 done in the form (C) chosen by the user (`CCA-DESIGN.md` §5):
  `ccacoh/Thm332` (Čech cover, induction with em/Exact); bridge
  `abelian` from the abelian Čech complex of stoneseq.  Announced.
- Degree-1 comparison as bijections of sets (user, 2026-10-24, after B5):
  `em/CorA07` (plain HoTT): Ȟ¹(X, Y, G) and H¹(X, Y, G) as set quotients
  (`Quotient`, by replacement), Ψ̄ injective (Lemma A.0.5, by path
  induction on psi d = psi d' with Lemma A.0.2 (ii)) and surjective
  (Lemma A.0.6), so Cor. A.0.7 = Prop. 3.1.4 (`corA07`); Cor. A.0.8
  (`A08.corA08`).  `ccacoh/Prop318Set`: Prop. 3.1.8 as Ȟ¹(X, S, G) ≃
  H¹(X, G).  Announced.  em 0.27 s, ccacoh 1.77 s (144 modules) cold;
  largest `--opened` in the new files 15 (`CorA07.surjective`).
- Not done, by the decision of §5: Appendix B on the Čech side (B.0.1,
  B.0.2, B.0.5, B.0.6, the missing B.0.7), Thm 3.3.2 as a group
  isomorphism; no group structure on Ȟ¹ / H¹ (only sets).
- Form (C') (user, 2026-10-24, after worker A found (C)'s hypothesis false
  for X = I): `ccacoh/Thm332C.thm332`: if Ȟ^(m+1)(X, S, A) = 0 for all m
  then H^(n+1)(X, A) = 0 for all n.  Higher Čech complexes on A's
  `cca/Cochains` (linked; its `Cech`, `Vanish k`; no complex of B's own) in `em/CechHigher`
  (naturality of δ, cone, chase, Ȟ¹ bridge to CechNA), `em/FibreTorsor`,
  `ccacoh/LiftStone` (part (2)), `Thm332.Step` generalised to take the
  connectivity of L.  Announced.  em 0.31 s (50 modules), ccacoh 1.82 s
  (149 modules) cold; largest `--opened` in the new files 26
  (`CechHigher.Shift.Chase.G.T.bound`).

## Continued by worker A (2026-10-24, B on other work; user's decision)

- Lemma B.0.1 (`em/CechZero`), B.0.2 = `CechHigher.Shift.vanishS`
  (README fixed), Lemma 3.1.5 as stated (`ccacoh/Lemma315`, with
  `em/CechPull`; `ScottCech.Stages` is now the instance of a general
  `ScottCech.Tower` of Stone spaces, same names for `H1Stone`), pointed
  versions of Cor. A.0.7, A.0.8, Prop. 3.1.8 (`em/CorA07Pt`,
  `Prop318Set.prop318-pointed`), ε = x ↦ K(ev_x) (`em/EpsEv`).  Next:
  Thm 3.3.2 as a natural group isomorphism (alongside `Thm332`,
  `Thm332C`, which stay).

## Gaps

(Log here every statement of the papers used without proof, omitted
verification, broken reference, or citation replaced by a proof.)

- DW1 Thm 2: only the existence half (as planned); uniqueness of
  deloopings is not proved.
- DW1 Lemma 3 and Lemma 9 are proved in the form used: the levels pass
  (Lemma 3), resp. Ω⁻¹ f is a retract of (a : A) → (b : B) × C a b
  (Lemma 9), not as equivalences.
- DW1 Cor. 5 (ii) only for m ≥ -1 (a subtype of A →pt B); DW1's m = -2 case
  (bi-invertible maps) is not needed: Cor. 6 uses Cor. 5 at levels
  n+m+1 ≥ -1 only.
- DW1 Cor. 12 only for n = 0 (A 0-connected, B 1-truncated), the case used;
  there Ω B is a set, so the pointing coherence is a proposition.
- DW1 §4.1, K(G, 2): DW1 sketches it via the centre Z(G) ("the loop space of
  the Σ-type is Z(G) ... the inclusion has a section iff G is abelian").
  Replaced by a direct proof: for A abelian, band_x⁻¹ ∘ band_0 deloops by
  Cor. 12 to K(A,1) ≃pt (K(A,1), x) (Whitehead), a homogeneous structure,
  so T K(A,1) is inhabited and Cor. 8 applies.
- CCA uses right G-torsors (Def. A.0.3); here left torsors (pn/Torsor's
  layout, so that for an abelian group they are pn's A-torsors by
  definition).  The formulas of Appendix A are mirrored and written without
  inverses (cocycle d y1 y2 . d y0 y1 = d y0 y2; trivial: g y1 . d y0 y1 =
  g y0).
- CCA Lemma 3.1.5 ("We omit the details"): now also proved as stated
  (`Lemma315`, worker A); originally in the form used by Lemma 3.1.6 only: cochains of pairs and triples on the limit are the
  colimits of the stage cochains (Props 2.3.5, 2.3.7); then the cocycle
  is represented at a stage and becomes a cocycle at a later stage (Φ₃
  injective).  As stated: injectivity is not by the paper's formulas for
  coboundaries but because restriction along a map of covers is injective
  on Ȟ¹ (`em/CechPull`: both are subsets of H¹ through Ψ).
- CCA Thm 3.3.2: "S is a Čech cover for X, A in the sense of ??" (broken
  reference): it is Def. B.0.3; proved from Thm 3.2.5 and Cor. 3.2.6
  (`Thm332.Over.Cov`), using that the fibres of S ->> X are Stone (X
  compact Hausdorff: closed equality, SSD Thm 4.18).
- CCA Prop. 3.1.8: X compact Hausdorff is not used (any X with a Stone
  S ->> X).  Proved in the vanishing form and as an isomorphism of pointed
  sets (G not abelian; `CorA07Pt`, worker A); the group structure for
  abelian coefficients belongs with Thm 3.3.2.
- CCA Def. 3.1.2 defines H¹(X, Y, G) as a subset of H¹(X, G); here it is
  the set quotient of the families with points over Y (Lemma 3.1.3), with
  its injection `forget` into H¹(X, G).  The quotients are taken at level
  l+ (Ȟ¹ is small, but one universe for both sides keeps Descend simple).
- CCA Thm 3.2.5 cites "the long exact cohomology sequence"; replaced by a
  proof: the fibre sequence K(A, m) ≃ Fib (K p m) (`em/FibSeq`, by
  induction on m with Ω Fib ≃ Fib Ω and Whitehead) and its exactness in
  the 0-connected form (`em/Exact`).
- CCA Thm 3.2.5: L(x) = A(x)^T(x)/A(x) "is a quotient of overtly discrete
  groups, and therefore overtly discrete" (no such lemma in SSD): L is
  represented as the image of the Čech differential A^T -> A^(T x T), a Σ
  of overtly discrete types and truncations (SSD Lemma 2.7, CCA Prop. 2.3.9).
- CCA Def. 3.2.1 ("the canonical map ε"): ε is defined by delooping
  (determined by its loopings); its identification with x |-> K(ev_x) is
  `em/EpsEv` (worker A): by induction, comparing loopings
  (`unique-loop`).
- DW1 Thm 2 / Cor. 7 use "Whitehead's principle [Uni13, 8.8.2]" only in
  the uniqueness half; for 0-connected types it is proved here
  (`em/Whitehead`).
- CCA Thm 3.3.2 is proved in the form (C') only (vanishing in all degrees
  from vanishing of all Čech groups), not degree by degree and not as a
  group isomorphism; Lemmas B.0.2, B.0.5, B.0.6 and the missing B.0.7 are
  replaced by the dimension shift in the vanishing form
  (`CechHigher.Shift`).  Čech cochains are A's ordered (augmented)
  cochains: all ordered tuples, degenerate ones included, as in Def. 3.3.1.
