# Solid modules over a finite ring (solid.pdf, internal part)

Target: `solid.pdf` (repo root `/Users/coquand/CANONICITY/solid.pdf`, 2 pages):
for a finite ring R, M(S,R) = lim R[S_n], Lemma 0.1, Lemma 0.2 and
**Theorem 0.1 (R is solid as an R-module)**, all inside synthetic Stone
duality (SSD.pdf, axioms 1-4), on top of the checked library `sag/stone*`.

Read first:
- `pdftotext -layout /Users/coquand/CANONICITY/solid.pdf` into your scratchpad;
- `/Users/coquand/CANONICITY/SSD.pdf` §1-§3 (only as needed: Lemma 1.12,
  Remark 1.20, Lemma 1.21, Lemma 3.1, Lemma 3.2, Cor 3.7, Thm 3.11);
- `sag/stoneseq/README.md` (table of what is proved, with names);
- `sag/stone/DESIGN.md`, `sag/STONE-INTERFACE.md`;
- `/Users/coquand/CANONICITY/seg/WRITING.md` (how files are written; follow it).

## Out of scope (do not attempt)

Projectivity of Z[N∞] / M(S,R), cokernels of solid modules, "solid modules
form an abelian category", "profinite modules are solid", Z_p.  These hold
only EXTERNALLY (they need LPO + DC in the metatheory) and cannot even be
stated internally (external projectivity is not stable under pullback), so
they must not appear as theorems or as Theory parameters.  Assume nothing
beyond the SSD axioms record `StoneAxioms.Assumptions` (duality, formal,
local, dc) and the Theory parameters of `stoneseq/All.seg` (univ, images,
surjections).

## Where to work

New directory `sag/solid/`, with its own `All.seg` written like
`sag/stoneseq/All.seg`: symlinks (`ln -s ../stone/X.seg` /
`../stoneseq/X.seg`) to the files needed, the same `module Theory (...)`
header and the same import order, then the new files appended.  Simplest:
symlink every file of `stoneseq/` (it already contains all of `stone/`) and
copy its `All.seg`, then append.  `sag/stone/` and `sag/stoneseq/` are
READ-ONLY.

Check from `/Users/coquand/CANONICITY/unit`:

    ./segc sag/solid changed        # after each edit
    ./segc sag/solid check M        # one file-module
    ./segc sag/solid all            # full check, at the end

Rules: every shell command under 60 s (use `timeout`); every single file
checks in under 10 s (an overrun is a defect: split the file / add lemmas);
do not commit, report to the user.  No ring solver: ring identities are
proved step by step as a mathematician writes them.  When reporting, say
whether Theorem 0.1 checks; say "no new axioms (Theory parameters univ,
images, surjections; SSD Assumptions)", never "no axioms".  Do not report
lemma counts.

## Existing results you will use (exact names)

- `Profinite.LimPres[X]` (E, p, finite, equiv : X ≃ DependentChoice.Lim E p),
  `Profinite.Over[ax].lemma31` : Stone X -> merely LimPres  (SSD Lemma 3.1).
- `DependentChoice.Lim E p` = compatible sequences; `SeqLim` (equality of
  points by components, maps of limits).
- `Lemma32`: a sequential limit of finite sets is Stone.
- `Cor37.Over[ax].Cor37[E,p,fin]`: `M.phi : colim (E n -> Nat) -> (Lim -> Nat)`,
  `injective`, `surjective f`, `equivalence`  (SSD Cor 3.7: every map
  lim E -> N factors through a stage; two stage maps equal on the limit
  agree at a later stage).
- `ImageClosed.Over[ax].Presented2[...].image-closed` : the image of a map of
  Stone spaces is closed (Thm 3.11); `StoneClosed.lemma310` : equality in a
  Stone space is closed; `StoneClosed.cor39`.
- `OpenClosed`: `isOpen`, `isClosed`, `closed-stable` (closed props are
  ¬¬-stable), `neg-closed` (¬closed is open, MP), `closed-or` (finite
  disjunction of closed props, uses LLPO), `closed-and`.
- `Omniscience...markov` (MP), `LLPO` (SSD 1.17).
- `Finite` (isFinite, FinEquiv, Uniform), `FinChoice.Fin`, `FiniteClosure`
  (Id, truncation, Σ of finite sets are finite; NOT function spaces).
- `Ring.CRing` (commutative rings), `RingHom`.
- For Lemma 0.1 only: `sag/freegroup` builds the free abelian group on a set
  as a filtered colimit of finite stages (Abelian.seg, FinSum.seg, README.txt),
  no HITs, quotients via replacement.  Port its pattern to R-modules.

## Design decisions (already settled)

1. **Fix a presentation.** Solidity is a proposition, so take
   S = Lim E p with E n = Fin (c n) (choose via lemma31 + countable choice,
   as Cor37 does with `enumerations`).  All sums are over Fin c in a fixed
   order: no invariance-of-sums lemma is needed.
2. **Solid via δ.** Define: L is solid for S iff restriction along the Dirac
   map δ : S -> M(S,R), Hom_R(M(S,R), L) -> (S -> L), φ ↦ φ ∘ δ, is a
   bijection.  This is the paper's definition composed with
   Hom(R[S],L) = L^S, and Theorem 0.1 does NOT need R[S] or Lemma 0.1.
3. **Lemma 0.2 without DC and without LLPO** (simpler than the paper).
   Claim: if y : E n is in the image of π^m_n for every m >= n, then y is in
   the image of π_n : S -> E n.  Proof: suppose not.  Then the maps
   [– = y] and 0 : E n -> N agree after composing with π_n, so by
   `Cor37...injective` they agree at some stage m, i.e. y is not in the
   image of π^m_n: contradiction.  So ¬¬(y ∈ im π_n); the image is closed
   (`image-closed`, E n is Stone by Lemma32 or directly as a finite set),
   and closed props are ¬¬-stable (`closed-stable`).
   Then Lemma 0.2: if u = λ_n μ and u(y) /= 0 (decidable, R finite), then
   for each m, y has a preimage x in E m with μ_m(x) /= 0 (finite search),
   so y ∈ im π^m_n for all m, so y ∈ im π_n.
4. **Factorisation of φ (Theorem 0.1, first line).** M(S,R) is itself a
   limit of the finite sets Fin (c n) -> R; with a code R ≃ Fin k ⊂ N, apply
   `Cor37...surjective` to code ∘ φ, then decode (clamp values outside
   Fin k to 0: π_n need not be surjective).  Similarly for g : S -> R.

## Steps

| step | file(s) | content |
|---|---|---|
| 1 | `FiniteRing.seg`, `RModule.seg`, `FinSum.seg` | finite commutative ring (CRing + carrier ≃ Fin k, decidable equality), R-modules, linear maps, Hom as a set, sums over Fin c with linearity and the single-nonzero-term lemma |
| 2 | `Measures.seg` | R^(Fin c) as a module; λ : R^(E m) -> R^(E n), (λu)(y) = Σ_{p x = y} u(x); M(S,R) = Lim of these, its module structure; δ : S -> M(S,R) and λ_n ∘ δ = δ ∘ π_n |
| 3 | `FunFinite.seg`, `Factor.seg` | Fin c -> R is finite (induction on c); every function M(S,R) -> R and S -> R factors through a stage (decision 4) |
| 4 | `Lemma02.seg` | decision 3 |
| 5 | `Theorem01.seg` | Theorem 0.1 as in the paper: ψ̃ (linearisation of ψ on R^(E n)) equals ψ on im λ_n; hence φ zero on δ(S) => φ = 0 (injectivity); g : S -> R factors as h ∘ π_n, and μ ↦ Σ_y h(y) (λ_n μ)(y) is a linear extension (surjectivity) |
| 6 | `Intrinsic.seg` | (after 5) presentation-free M(S,R) := Hom_R(R^S, R) and M(S,R) ≅ lim via Cor 3.7 for R-valued maps and self-duality of R^E, E finite; Theorem 0.1 for every Stone S |
| 7 | `FreeModule.seg`, `Lemma01.seg` | (last, optional) free R-module R[S] on a set (port of freegroup), R[S] -> M(S,R) injective (Lemma 0.1): distinct points are separated by a decidable subset (lemma310 + neg-closed/MP), the merge step e1 = ei by closed-or (LLPO) + closed-stable; induction on the number of terms; then the paper's definition of solid is equivalent to decision 2 |

Stop after step 5 and report whether Theorem 0.1 checks; continue with 6, 7
only if the user says so.

## Paper gaps to record

Keep a "Gaps" section at the end of this file.  Known so far:
- Theorem 0.1 uses λ_n ∘ δ = δ ∘ π_n silently (φ(v_i) = ψ(λ_n(v_i))).
- Lemma 0.2 does not need DC or LLPO (decision 3).
- "Since R is finite, φ factors through λ_n" is Cor 3.7 applied to the Stone
  space M(S,R), via a code of R in N.

## Gaps

- The factorisation of a function on measures uses Corollary 3.7 for the
  tower of finite vector sets. Splitting off the first coordinate proves
  their finiteness. Extending the inverse ring enumeration by zero gives
  a total decoder, including on stage vectors outside the projection image
  (`FunFinite.Values.finite`, `Factor.Tower.measure-factor`).
- In Lemma 0.2 a nonzero fibre sum supplies a nonzero summand at every
  later stage. If the index were missing from the limit, its indicator
  and zero would define the same colimit class by Corollary 3.7. Their
  agreement at a later stage contradicts that summand. The image is
  closed by SSD Corollary 3.13 applied to the decidable projection fibre.
  Closed stability finishes the argument without a separate application
  of DC or LLPO in this deduction (`StageImage.Tower.AtPoint.persistent`).
- The identity λₙ(δₓ) = δ_{πₙ(x)} follows by summing a single point mass
  (`Measures.Tower.project-dirac`). Finite choice supplies lifts for the
  nonzero coefficients. A zero coefficient contributes the zero measure
  without requiring a point over its index. The resulting sum has the
  same stage projection as the original measure, which suffices to
  compare their functional values (`Lemma02.Tower.AtStage.project-lifted`,
  `Theorem01.Tower.Linearisation.AtMeasure.on-image`).
