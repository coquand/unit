# Worker B: sequential colimits, cohomology base, then SSD §5.2

Read first: `stone/DESIGN.md` (rules, representation choices),
`../STONE-INTERFACE.md`, the paper `SSD.pdf` (repository root; its text can
be extracted with `pdftotext`), and `pn/Torsor.seg`, `pn/Cech.seg`,
`pn/Vanish.seg`, `pn/Coboundary.seg` (SAG §7.4, reused here). You own
`sag/stoneseq/` only. Worker A works in `sag/stone/` at the
same time. Your files do not depend on the Stone axioms except through
explicit hypotheses (dependent choice as a module parameter): keep them
generic.

## Steps

- **B0. Skeleton and DependentChoice (first, A waits for it).**
  `stoneseq/All.seg` like `exterior/All.seg` (symlinks to `../pn/`). Then
  `stoneseq/DependentChoice.seg` with `Lim`, `proj0`, `Surjective`, `DC`
  exactly as fixed in `../STONE-INTERFACE.md`; announce it as stable there.
- **B1. Sequential colimits and limits of sets.** Colimit as a set quotient
  of Σₙ Aₙ with `inc`, `glue`, induction into sets, and effectiveness
  (inc n x = inc m y iff they become equal at some later stage); limits as
  compatible sequences. The facts SSD takes from [18] for sets: Σ-types,
  identity types and propositional truncation commute with sequential
  colimits. Finite sets (merely ≃ Fin k). SSD Lemmas 2.3, 2.4, Corollary 2.5,
  Lemmas 2.6, 2.7 (using DC as a hypothesis). Announce stable.
- **B2. Cohomology base.** The integers Z as an abelian group with decidable
  equality; abelian groups as needed; "a sequential colimit of exact
  sequences of abelian groups is exact"; SSD Definitions 5.3, 5.4 (Čech
  complex of S, T, A for arbitrary types) and Lemmas 5.5, 5.6, 5.7 (5.7 via
  `pn/Torsor.seg`, BZ = Z-torsors). Announce stable.
- **B3. Join with A** (needs A's Remark 3.4, Corollary 3.7, Theorem 4.18,
  symlinked from `stone/` once announced): SSD Lemma 5.8, Lemma 5.9,
  Lemma 5.10 (H¹(S,Z) = 0 for S Stone, i.e. every map S → BZ is merely
  trivial), Corollary 5.11.
- **B4.** SSD §5.3 (Lemmas 5.13–5.15, Theorem 5.16): first write in
  DESIGN.md §5 which form of Theorem 5.16 is feasible, and ask the user
  before starting it.

Done when each step checks under `./segc sag/stoneseq changed`, every file
< 10 s, and a short `stoneseq/README.md` lists what is proved, with SSD
numbering.

## Gaps

(Log here every statement of the paper used without proof, or citation
replaced by a proof.)

- **Remark 2.2 / [18] Cor. 7.7.** Not proved: sequential colimits are
  *defined* as in set theory (quotient of Σₙ Aₙ by "eventually equal",
  `SeqColim.seg`), so overtly discrete types are sets by definition. The
  comparison with the HoTT sequential colimit would need HITs, which the
  library does not have.
- **[18] Thm 5.1, Thm 7.4, Cor 7.7** (Σ, identity types, truncation commute
  with sequential colimits) are replaced by proofs for the set-level colimit:
  `SeqSigma.SigmaColim` (Σ of a family of sets over the colimit),
  `SeqSigma.SigmaFamily` (Σ over a fixed set of a family of sequences, also
  needed), `SeqProp.IdColim`, `SeqProp.TruncColim`, `SeqProp.PropColim`.
- **Lemma 2.3** (no proof in the paper). Proved with countable choice only
  (derived from DC, `CountableChoice.cc`), and in a stronger form: the
  presentation of the source is kept, only the target is reindexed by a
  cofinal subsequence (`SeqSub.seg`: a cofinal reindexing has the same
  colimit, also not in the paper). Lemma 2.6's proof needs this form.
- **Lemma 2.4** (no proof). Proved (`Lemma24.seg`); it uses that colimits of
  levelwise injective (surjective) maps are injective (surjective)
  (`SeqMaps.seg`).
- **Corollary 2.5** (no proof). Needs that images of maps between finite
  sets are finite; proved without decidability (`FiniteClosure.seg`:
  identity types, truncations and Σ of finite sets are finite, by induction
  on `Fin k` and univalence).
- **Lemma 2.6** ("using Lemma 2.3 and dependent choice"). Needs (a) DC in
  relational form (`CountableChoice.Relational`), (b) DC at level `l+`,
  since presentations are large, (c) the diagonal lemma: the colimit of a
  grid of sequences is the colimit of its diagonal (`SeqGrid.seg`, ~200
  lines; not in the paper).
- **Lemma 2.7.** The Σ case is not "by closure of finite sets": the fibres
  over a stage are only overtly discrete, so it needs a finite-Σ lemma
  (finite choice of presentations, at level `l+`), then Lemma 2.6. Also
  uses univalence (`Torsor.eqind`) to move statements along `X = colim S`.
- **Remark 5.2.** BG is taken to be the type of G-torsors (`pn/Torsor`,
  `TorsorId`: a delooping of G), and "H¹(X, G) = 0" is stated without the
  set truncation as `CohZero`: every family of torsors is merely trivial.
- **Definition 5.4.** Ȟ¹ as the quotient group ker d1 / im d0 is not
  formalised (B4 may need it); "Ȟ¹(S, T, A) = 0" is exactness at C1, as the
  paper remarks after the definition (`Cech.H1Zero`). Cocycles are stated in
  the additive form b(u,v) + b(v,w) = b(u,w), shown to give d1 b = 0
  (`cocycle-d1`).
- **Lemma 5.7.** Stated with points of the torsors (beta x u : alpha x)
  instead of paths alpha x = *. The conclusion is mere
  (|| (x : S) -> alpha x = * ||): the coboundary given by Ȟ¹ = 0 is mere. The
  last step ("beta' constant on T x gives a path from || T x ||") is the
  factorisation of a weakly constant map into a set through the truncation
  (Kraus), not stated in the paper.
- **"A sequential colimit of exact sequences is exact"** (Lemma 5.9, no
  proof in the paper): proved for maps of sequences preserving chosen points
  (`ExactColim.seg`); only the zeros are used, not the group structure.
- **Lemma 5.8** ("the usual correspondence between surjections and families
  of inhabited types"). Stated as: Σ T -> S is merely a limit of levelwise
  surjections g k : E k -> G k of finite sets (Remark 3.4 on the first
  projection, Σ T Stone by Theorem 4.18). The finite families T k are the
  fibres of g k, and the limit family is the fibre of lim g, not the limit
  of the fibres (FibreSeq): this avoids transport in a limit of fibres. The
  passage back to T is CechTransfer (T x = fibre of the projection = fibre
  of lim g over eY x, by a square of equivalences).
- **Lemma 5.9.** "By Corollary 3.7, Č(S, T, Z) is the colimit of the
  Č(S k, T k, Z)": Cor. 3.7 (worker A) is for N-valued maps on a limit of
  finite sets; here it is applied to the fibre products E2 k, E3 k of g k,
  through the enumeration Z = N (`Integers.toNat`) and the identification of
  the Čech groups of a family of fibres with functions on fibre products
  (`FibrePairs.tau1`, `tau2`), natural in k. Only "Φ₁ onto, Φ₂ injective" is
  proved and used, not "Φ is an equivalence".
- **Lemma 5.10** uses local choice in A's form (for Sp B, B : Booleω); the
  family T is the fibre of the chosen surjection Sp C -> Sp B, Stone by
  Theorem 4.18, Lemma 3.10 and Corollary 3.9.
- **Corollary 5.11.** The canonical map B(Z^S) -> (BZ)^S is not formalised
  (it needs change of group for torsors, not in `pn`). Proved instead: (BZ)^S
  is connected (Lemma 5.10) and its loops at the trivial family are the
  group Z^S (`Cor511`), i.e. (BZ)^S is a delooping of Z^S. "Embedding" is
  then automatic; the identification of a delooping with Z^S-torsors is the
  general fact not formalised here.
- **Theorem 5.16** (forms (A) and (B) of stone/DESIGN.md §5). Proved
  directly with the torsor of a cocycle (pn/Torsor `Tors.psi`, SAG Lemma
  7.4.2), not through Lemmas 5.13-5.15 and long exact sequences, which are
  not formalised. Of the Čech cover only "S x merely inhabited" and
  "(x : X) * S x Stone" are used (X need not be compact Hausdorff). Ȟ¹ and
  H¹ are quotients (pn/Quotient, by replacement) at level l+; the bijection
  is of sets, without the group structures.


## --opened audit (seg/WRITING.md rule 6)

Run after each file: `segd All.seg --opened --only FILE` (the checker of this repository).
Declarations above ~500 openings, and the fix (2026-10-24):

- `SeqSigma.SigmaColim.Reflect.over` 3017, `Reflect.meet` 2118, `iter-B` 1908:
  points of Tot were variables `u`, so `B (cls u)` against `B (inc u.1 u.2)`
  was settled by eta through the quotient (Tot, Rel, Quot.image). Fixed by
  stating points by their components (`pt n x b`) and the stage form of
  `inc-iter` once in SeqColim (`inc-shift d n x`). Now 306 / 452 / below 250.
- `Lemma26.Built.toOuter` 2724: wrote `(path.2 n).2` instead of the names
  `P`, `Sg`, `Hg`. Fixed by naming `square` once. Now below 250.

B3 (2026-10-24): every declaration below 500 except two first uses of a
module instance: `Lemma59Fibres.nat1-at` 530 and `Lemma59Stone.FromLimit.over`
544. In both, ~415 openings (`Lemma59.L`, `Cech.C0/C1/C2`, `seq0..2`) are a
one-time cost of forcing the instance: a copy of `nat1-at` placed after it
opens 115. Naming the transition maps of the fibre products (`FibreSeq.p2`,
`p3`) brought `nat1` from 624 down.

Largest remaining (B1-B2, all < 0.01 s): `Lemma26.Built.surjective` 405,
`Lemma59.R2` 400, `SeqSigma.Reflect.over` 306, `SeqGrid.value-step` 281
(`Le` unfolded: the witnesses are pairs built inline).
