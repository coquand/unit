# Synthetic Stone duality : design

Paper: Cherubini, Coquand, Geerligs, Moeneclaey, *A Foundation for Synthetic
Stone Duality* (TYPES 2024), `SSD.pdf` at the repository root. Model for the
whole project: the SAG formalisation (`seg/notes/sag.tex`, axioms as a record
of module parameters in `pn/SAGAxioms.seg`).

Status (2026-10-24, worker A): SSD §1 done; §2.2-§3 and §4.1-4.3 up to
Theorem 4.18 done (with the deviations listed in HANDOFF-A.md "Gaps");
whole directory 3264 declarations, 0.99 s. See §6.

## 1. Scope and order

Steps 1–5 of the plan (the interval, real numbers and Brouwer, SSD §4.4,
§5.4–5.5, are out of scope for now):

1. Boolean algebras, Booleω, Sp, the axioms record (SSD §1.1–1.3).
2. SSD §1.4–1.6: ¬WLPO, MP, LLPO, open/closed propositions.
3. SSD §2–3: overtly discrete types, Stone spaces as profinite sets,
   Theorem 3.11.
4. SSD §4.1–4.3: compact Hausdorff spaces up to Theorem 4.18.
5. SSD §5.1–5.3: Čech complexes, H¹(S,Z) = 0 for S Stone (Lemma 5.10),
   Corollary 5.11; Theorem 5.16 decided later (see §5 below).

## 2. Two workers, two directories

| | owns | first track | after the join |
|---|---|---|---|
| **A** | `stone/` | Boolean layer, axioms record, SSD §1 | SSD §2.2–2.3, §3, §4.1–4.3 |
| **B** | `stoneseq/` | sequential colimits/limits, dependent choice; integers Z, exactness of sequential colimits, generic Čech lemmas 5.5–5.7 | SSD §5.2 (Lemmas 5.8–5.10, Cor. 5.11), then §5.3 |

Join points: A needs B's sequential colimits for SSD Lemma 2.13 onwards; B
needs A's §3–4 (Remark 3.4, Theorem 4.18, Corollary 3.7) for Lemma 5.8.
Each side announces finished, stable files in `../STONE-INTERFACE.md`; the
other side then symlinks them into its own directory (never edits them).

## 3. Rules (as for SAG)

- **Checker:** the one in this repository (`cabal build` at the root);
  check with **`./segc sag/DIR changed|all`** from the root. If the checker
  was rebuilt, run `./segc sag/DIR stop` so that the next call starts a
  server on the new binary.
- **Write so that checking follows reading**: `seg/WRITING.md` (informal
  proof first, one name per notion, "by definition" facts stated once by
  `refl` next to the definition, write the common point of a definitional
  step, accessors instead of projection chains). After each declaration,
  `--opened` (and `--opens F`) on the file: a declaration that opens much
  more than its text says is a defect even when it is fast.
- Each worker edits only its own directory. Shared files (`pn/`, `torsor/`,
  `core/`, …) are read-only; symlink them. A needed change to a shared file,
  or moving a file between directories: ask the user first.
- `All.seg` per directory, built like `exterior/All.seg` (the `Theory` module
  with `univ`, `images`, `surjections`; symlinks to `../pn/` for the shared
  foundation). Check with `./segc sag/stone changed` / `./segc sag/stoneseq changed`
  from the root.
- Every file < 10 s; every shell command < 60 s (strict timeouts).
- Conventions of the library: recursion only through eliminators
  (`PRIMREC.md`); no type classes; no HITs (quotients and truncation come from
  replacement); general statement first, instance second; lock a construction
  right after its characterising lemmas.
- Do not commit: the user commits. Do not touch other directories' files or
  the user's pending changes.
- Keep a log of every gap in the paper that the formalisation has to fill
  (statement used without proof, citation replaced by a proof) in a
  "Gaps" section of the worker's handoff file. This is a deliverable.

## 4. Representation choices (both workers follow these)

- **Axioms.** One record in `stone/StoneAxioms.seg` (A), with level
  parameters as in `pn/SAGAxioms.seg` (`ZChoice` has a level `k` for the
  family):
  - `duality`: for B : Booleω, the evaluation B → (Sp B → 2) is an
    equivalence;
  - `formal`: for g : B → C in Booleω, g injective iff precomposition
    Sp C → Sp B is surjective;
  - `local`: local choice (SSD Axiom 3), for families in `U k`;
  - `dc`: dependent choice (SSD Axiom 4), **defined by B** in
    `stoneseq/DependentChoice.seg` (B writes this file first; see the
    interface).
- **Booleans.** `Bool` with decidable equality; Boolean algebras as a record
  (set carrier, 0, 1, ∧, ∨, ¬, laws) or as Boolean rings — A decides, records
  it here.  **Decided (A): Boolean rings** (`stone/BooleanRing.seg`): record
  `BA { ring : CRing ; set ; idem }` over `Ring[l].CRing` (whose `Nat` is
  not used: everything is on `Base.Nat`); x /\ y = x y, not x = 1 + x,
  x \/ y = x + y + x y, x <= y iff x y = x; morphisms are ring morphisms
  (`RingHom`).  2 = Bool with xor/and. The free algebra 2[I] on a finite I with decidable equality
  (e.g. truth tables on 2^I, or normal forms); 2[N] as the colimit or directly
  with elements "a finite k and a function on 2^k". Equality decidable in
  2[N] is needed (¬WLPO, LLPO use normal forms in B∞).
- **Countably presented**: generators N, relations a sequence r : N → 2[N];
  quotient as a set quotient by x ~ y iff x ⊕ y ≤ some finite join of the rₙ.
  Booleω as a type of algebras merely having such a presentation (like
  finitely presented algebras in SAG).
- **Countable / finite**: countable = merely equal to a decidable subset of N
  (SSD Def. 1.2); finite set = merely equivalent to `Fin k`.
- **Sequential colimits and limits** are of sequences of *sets*; colimit as a
  set quotient of Σₙ Aₙ, limit as compatible sequences. All SSD uses of [18]
  (Sojakova–van Doorn–Rijke) are for sets and become lemmas proved by B.
- **Integers** Z: B's choice (data type with normalised constructors or a
  quotient), as an abelian group with decidable equality.
- **BZ** = Z-torsors as in `pn/Torsor.seg` (SAG Lemma 7.4.2), which is
  essentially SSD Lemma 5.7.

## 5. Open decisions

- Theorem 5.16 (H¹(X,Z) ≅ Ȟ¹ as groups) needs set truncation, a group
  structure on H¹ and long exact sequences. Decide after step 4 whether to do
  the full statement or only "H¹(X,Z) = 0 iff Ȟ¹(X,S,Z) = 0" / a bijection of
  sets.

  **Worker B's assessment (2026-10-24, after B3).** Three forms, in order of
  cost. All three need of the Čech cover (X, S) only that each S x is merely
  inhabited and Σ S is Stone (X need not be CHaus).
  (A) *Vanishing form*: CohZero X Z <-> Ȟ¹(X, S, Z) = 0 (exactness at C1).
      Feasible now, about 2 files.
      - <=: given alpha : X -> BZ, Lemma 5.10 on Σ S gives mere points of
        the alpha x over S x; then Lemma 5.7.
      - =>: a cocycle b defines the family of Z-torsors
        alpha_b x = { f : S x -> Z | f v - f u = b x u v } ("local
        potentials"). It is a torsor: Z acts by adding constants, and it is
        merely inhabited by f = b x t _ for t : S x (Lemma 5.5). Two points
        differ by a map constant on S x, hence by an integer (ConstantMap).
        If alpha_b is merely trivial, its points form a cochain a with
        d0 a = b.
  (B) *Bijection of sets*: ||X -> BZ||_0 = Ȟ¹(X, S, Z), with the set
      truncation and the quotient group ker d1 / im d0 both as quotients
      (pn/Quotient, by replacement). [b] |-> alpha_b is well defined and
      injective (alpha_b = alpha_b' iff b - b' is a coboundary, via
      TorsorId.decode), and surjective (as in (A) <=: Lemma 5.10 on Σ S, then
      alpha = alpha_g for the cocycle g of Lemma 5.7). Feasible, about 3-4
      files beyond (A). It does not give the group structure on H¹.
  (C) *Group isomorphism by the paper's route* (Lemmas 5.13-5.15): needs
      the groups Z^(S x)/Z (quotients), H⁰ and H¹ of X with coefficients in
      a family of groups (as groups, so the contracted product of torsors),
      and long exact sequences in cohomology. Much larger, and not needed by
      §5.4 if 5.19 is stated in form (A) (H¹(I, Z) = 0).
  Both (A) and (B) argue directly with the torsor of local potentials, not
  through the paper's exact sequences (log in HANDOFF-B "Gaps"). B
  recommends (A), then (B); (C) only if group structure is wanted later.
- §4.4 and §5.4–5.5 (reals, Brouwer) are out of scope; Brouwer uses the
  localisation modality L_I, a HIT, which would need either a hypothesis or a
  reformulation.

## 6. Worker A: what is proved (SSD numbering)

Files in `stone/`, in import order (see `All.seg`):

- `BooleanRing`: Boolean algebras as Boolean rings, laws (x + x = 0, Shannon
  combinations), morphisms preserve them; the algebra 2.
- `FreeFinite`: 2[Fin k] as truth tables `Tab k` (Tab (k+1) = Tab k x Tab k),
  its universal property Hom(2[Fin k], B) = B^k.
- `FreeCountable`: 2[N] as the functions 2^N -> 2 that merely come from a
  truth table; universal property Hom(2[N], B) = B^N; **Example 1.8 (iii)**
  (`cantor`: Sp(2[N]) = 2^N, a point is evaluation); `agree` (an element
  depends on finitely many bits); the shift g n |-> g (n+1).
- `QuotientBA`: B/I for an ideal I, universal property.
- `Presented`: the ideal generated by r : N -> B, B/(r), Hom(B/(r), C) =
  morphisms killing every r n; countably presented algebras and **Booleω**
  in the form of **Remark 1.4** (merely isomorphic to 2[N]/(r)); **Def. 1.7**
  Sp; Sp(2[N]/(r)) = {alpha | r n (alpha) = 0}; points, generator
  extensionality, inverse of an isomorphism.
- `Examples`: **Example 1.6** (2 initial), **1.8 (i), (ii)**, **Lemma 1.9**,
  B∞ and N∞ (**1.8 (iv)**, with the presentation g n /\ (g 0 \/ .. \/ g (n-1))).
- `TwoPresented`: 2 = 2[N]/(g n), so 2 : Booleω; every 2[N]/(r) is in Booleω.
- `Product`: A x B, Sp(A x B) = Sp A + Sp B.
- `BinfFacts`, `NoRetraction`: standard points of N∞ decide the ideal of B∞
  (instead of the normal form of 1.8 (iv)); f : B∞ -> B∞ x B∞;
  **Lemma 1.18** (`no-retraction`).
- `BoolSeq`: bounded joins, joins over squares, first hits.
- `StoneAxioms`: **Axioms 1-4** as the record `Assumptions` (`duality`,
  `formal`, `local`, `dc`), levels `l k` as in `pn/SAGAxioms.seg`.
- `StoneDuality`: **Lemma 1.12**, **Corollary 1.13**.
- `Omniscience`: **Theorem 1.14** (`not-wlpo`), **Theorem 1.15**,
  **Corollary 1.16** (`markov`).
- `ProductPresented`: Booleω is closed under binary products (needed for
  1.17; uses Axiom 1).
- `LLPO`: **Theorem 1.17** (`llpo`).
- `OpenClosed`: **Def. 1.19**, **Remark 1.20**, **Lemma 1.21** (finite
  parts; countable parts given countable choice, `Countable[cc]`),
  **Corollary 1.22**, **Lemma 1.23** (given countable choice), **Lemma 1.24**,
  **Def. 1.25**, **Remark 1.26**.
- `Remark110`: **Remark 1.10**: Hom(A, B) = (Sp B -> Sp A) for A, B : Booleω.
- `Lemma28`: **Lemma 2.8**.  `CantorStages`, `Profinite`: Stone spaces,
  **Lemma 3.1**.  `Blocks`, `Tabulate`, `FinBool`, `LimCode`, `Lemma32`:
  **Lemma 3.2**.  `FiniteCode`, `Cor37`: **Lemmas 3.5, 3.6, Corollary 3.7**.
- `DecFree`: decidable equality of 2[N].  `StoneClosed`: **Corollaries 3.8,
  3.9, Lemma 3.10**.  `ImageClosed`, `Thm311`: **Theorem 3.11** ((i), (iv),
  (v); (i) gives (iii)), **Corollaries 3.12, 3.13, 3.14**.  `Lemma316`:
  **Lemma 3.16**.  `Pairing`: Cantor unpairing, enumeration of 2[N].
  `Spread`, `Remark34`: **Remark 3.4** for surjections.  `Compact`:
  finite subcovers of countable decidable covers.  `StoneProduct`:
  **Corollary 3.3** for binary products.
- `CHaus`: **Definition 4.1, Lemma 4.2, Corollaries 4.3, 4.4, Lemmas 4.5,
  4.9**.  `Sigma411`: **Lemma 4.10** (one direction), **Lemma 4.11**.
  `PowerSet`, `Lemma412`: **Lemma 4.12**.  `Components`: **Definition 4.13,
  Lemmas 4.14, 4.15, 4.16**.  `Thm418`: **Lemma 4.17, Theorem 4.18**.

Not done: Def. 1.3 for arbitrary countable I, J (reduction to Remark 1.4);
"Sp is an embedding" and the dual equivalence of categories (Remark 1.10,
second half); Remark 1.11 as a statement (used in the proof of 3.11);
Lemmas 2.12, 2.13, Corollary 2.14, Remarks 2.15, 2.16 (not needed: 3.11
and 4.12 are proved without them, see the gaps); Remark 3.4 for arbitrary
maps and injections; Corollary 3.3 beyond binary products; Remark 3.15;
Lemma 4.10 (converse); Corollaries 4.6, 4.7, Remark 4.8.
