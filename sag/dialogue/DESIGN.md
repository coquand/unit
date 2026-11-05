# sag/dialogue: translating DialogueTreesHeight to Unit

Goal: a complete Unit translation of Escardó's DialogueTreesHeight
(the height of the dialogue tree of every System T term of type
(ι⇒ι)⇒ι is below ε₀, and ε₀ is the least such bound), with a cleaner
architecture.  Only parameter: function extensionality (`fe`, see All.seg).
No new axioms, no postulates.

## Sources (read-only)

Agda sources: github.com/martinescardo/DialogueTreesHeight (master, 2026-11-05) and
github.com/martinescardo/TypeTopology at commit ee4e4c86 (the one the README names).
During the translation they were cloned to a temporary scratchpad:

    S=/private/tmp/claude-501/-Users-coquand-CANONICITY/33901f29-8ce7-4178-862f-bd7755374176/scratchpad/agda
    $S/DialogueTreesHeight/source/DialogueTreesHeight/{BrouwerOrdinals,DialogueTrees}/*.lagda
    $S/DialogueTreesHeight/source/DialogueTreesHeight/index.lagda   (outline of the proof)
    $S/TypeTopology/source/EffectfulForcing/MFPSAndVariations/*.lagda
    $S/TypeTopology/source/Ordinals/{BrouwerCodes,ChurchEncoding}.lagda

Code is between `\begin{code}` and `\end{code}`.

## Architecture (the improvement over the Agda)

The Agda proves three "fundamental theorems" by three separate inductions
on terms.  Here there is ONE generic lemma, `SystemT.Fund`, and three
instances:

1. `SystemT.seg`: `record Model` (values `V t`, `ap`, constants
   zero-v succ-v omega-v iter-v k-v s-v); `Eval[M].ev`; `record Rel (M N : Model)`
   (a logical relation: `R`, `r-ap` respecting application, one field per
   constant); `Fund[M,N,Q].fund` relates `Eval[M].ev e t h` and
   `Eval[N].ev e t h` for every typed term.
2. `Models.seg`: `PM` (pointwise set model), `DM` (dialogue model),
   `LR : Rel[PM, DM]`  =  Escardó's main-lemma, giving `dialogue-correct`.
3. (to do, step 2) the majorant model `MajM` (`V ι = Br`, `V (σ⇒τ) = V σ → V τ`,
   Agda `Majorant.lagda` `Maj`, `μ-…`) and `Rel[DM, MajM]` with
   `R ι x a = Le (height x) a` (Agda `Majorant.R`, `R-Zero` … `R-S`, plus the
   recursor clause from `MajorantAll`).  Fund gives  height(tree t) ≤ μ t.
4. (to do, steps 3–4) the tuple model `TupM`: values at σ are graded tuples
   `Tup (wd σ)` with `All<` (entries < ε₀) (Agda `MoveTuple`, `Rect…`);
   application `rect ∘ rdOf`; constants the tuples of Agda `Fundamental.fundamental`
   (`zeroTup`, `dI`, `dS`, `(S Z, (Z, ⋆))` for Ω).  Agda `Predicate.Dom`
   becomes `Rel[MajM, TupM]`; its fields are the clauses of `Predicate`,
   `SClause`, `IterClause`.  Fund gives μ t ≤ tsum (tuple t) < ε₀.

Theorem = composition: height(tree t) ≤ μ t ≤ tsum(tup t) < ε₀.
Then sharpness (Agda `Sharpness`, `Examples`, Church encodings) and a
`Theorems.seg` restating the four results of `Main.lagda`.

If the Agda's own formulation does not fit `Model`/`Rel` exactly (e.g. an
existential over tuples), adapt the model (e.g. values = Σ tuple, All<) so
that it does; record the adaptation in the file comment.  If something
genuinely cannot be phrased this way, stop and report rather than force it.

## Plan and file names

| step | Agda modules | Unit file(s) |
|---|---|---|
| done | CombinatoryT, Dialogue, MFPS-XXIX, BrouwerCodes, Order (≤, ⊕), Constructive (height) | SystemT, Dialogue, Models, Brouwer, Height, Examples |
| 1 | Order (rest), Multiplication, Epsilon0, MultClosure | Ordinals.seg / Epsilon0.seg / MultClosure.seg (split as convenient) |
| 2 | Majorant, MajorantAll | Majorant.seg |
| 3 | MultAffine, Absorb, Move, MoveTuple, Cascade, CascadeLevel, Rect, RectAdd, RectAlgebra, RectSum, RectApply, RectCurry, RectOrbitAct | Tuples*.seg (consider a record for the graded-map algebra if it shortens; otherwise follow the Agda) |
| 4 | Predicate, SClause, IterClause, Fundamental | Bound.seg (TupM, Rel[MajM,TupM], the theorem height < ε₀) |
| 5 | Examples (repo), ChurchEncoding (TypeTopology), Sharpness, Main | Sharpness.seg, Theorems.seg |

Article.lagda (paper index) is not translated.

## Existing Unit names to reuse

- `Brouwer.seg`: `data Br = Zb | Sb (b) | Lb (f : Nat -> Br)`; `Le` (recursive,
  see below); `le-l`, `le-refl`, `upper`, `le-L-mono`, `le-trans`;
  `add a b` (= Agda `a ⊕ b`, recursion on b).
- `Height.seg`: `height`, `height-relabel`, `height-kleisli`, `height-generic`.
- `Dialogue.seg`: `D`, `B`, `kleisli`, `fmap`, `generic`, `decode`, …
- `Models.seg`: `iterN`, `SetV`, `SetM`, `PM`, `BV`, `KE`, `DM`, `LR`, `tree`, `FT`.

Agda's `≤` is an inductive family (`≤-Z ≤-S ≤-ℓ ≤-L`).  Here `Le` is
defined by recursion with the same meaning:
`Le Zb b = Top`; `Le (Lb f) b = (n) -> Le (f n) b`;
`Le (Sb a) Zb = Empty`; `Le (Sb a) (Sb b) = Le a b`;
`Le (Sb a) (Lb g) = (n : Nat) * Le (Sb a) (g n)`.
So `≤-Z` is `tt`, `≤-S p` is `p`, `≤-L` is a function, `≤-ℓ n p` is
`le-l a f n p`.  Proofs by pattern matching on ≤-derivations become
inductions on the codes (see `le-trans`: helpers `trans-S`, `trans-SS`).
Define `a < b` as `Le (Sb a) b` (as in the Agda's Epsilon0, check).

## Unit idioms and pitfalls (measured in this project)

- Read `/Users/coquand/CANONICITY/seg/WRITING.md` before writing.
- Check with the server: `cd /Users/coquand/CANONICITY/unit && ./segc sag/dialogue changed`
  (all: `./segc sag/dialogue all`).  EVERY shell command under 60 s (`timeout 55`).
- No indexed inductive families, uniform parameters only, no mutual data.
- Recursion only through `split` with recursive results (`suc n | r ->`).
  A `split` must be the body of a definition (after its λs) or a branch of
  a split; never in `where`/`let`.  A split on a pattern variable nested in
  a branch whose type is not a Π fails ("cannot infer a type"): write a
  helper definition taking that variable, or `\ x -> split {…}`.
- Hidden arguments `{x}` are filled without unification: `transH (apH f p) q`
  can fail; use `calc A { a =< p > b =< q > c }` (writes every point).
- Paths[l]: `symH transH apH substH happlyH`; Prelude[l]: `idJ`, `Sigma-eq`,
  `absurd (A) e`, `isProp` …; funext: `module FL = Axioms[l].FunExtLemmas[fe @l]`,
  `FL.funext A B f g h`.
- Record instances: `new R[params.., field1, field2, ..]` (params first, in
  the same bracket), or named `new R[f := .., g := ..]`.
- A file named like a record/definition it declares clashes (rename the file).
- `open M` is not re-exported: refer to `M.N.x` from other files.
- Constructors of a data type in another module are not reachable as
  `M.ctor` in terms; `open` that module or define helper functions.
- Decidable choices on Bool: see `sag/freegroup/Decisions.seg` (`cases`,
  `so`); link it if needed.
- No ring solver: ordinal laws are proved by explicit induction and calc.
- Keep files checking at every step; report `./segc sag/dialogue all`
  output, file sizes, and max `--opened` (`seg All.seg --opened`).

## Progress log

- Step 1 done: Ordinals.seg (Multiplication: numB omega mul …), Epsilon0.seg
  (wexp tower eps0 Lt, closure lemmas; generic MonoRight, Closure2.close),
  MultClosure.seg.  Names: Agda `ι[n]`=numB, `ω`=omega, `⊗`=mul, `ω^`=wexp,
  `ε₀`=eps0, `<`=Lt (Lt a b = Le (Sb a) b), `_+ℕ_`=plusN, `maxℕ`=maxN, `_≤ℕ_`=leN.
- Step 2 done: Majorant.seg: MV (Maj), MajSup, MajAdd, mu-kleisli, mu-…,
  MajM : Model, RH, HR : Rel[DM, MajM], height-le-mu, muTree,
  dialogue-tree-height-le-mu, dialogue-height-lt-eps0.
- Identifier note: `+` is not an identifier character (x+ → xpos).
  Rel fields can be filled with separately named clause lemmas whose types
  reduce to the field types.
- Step 3a done (MultAffine, Absorb, Move, MoveTuple, Cascade, CascadeLevel,
  Rect, RectAdd): Affine.seg (pw, pw-wexp, mul-two, dbl-wexp, module
  LimitMult[M, Mpos, dbl]: crux mbody pw-pos orbit-inv; FinMult (⋖), fm-base
  fm-add fm-mul fm-le-omega fm-omega), Moves.seg (ValidMult, record Move
  {mt ms mt-lt ms-pos ms-lt mvalid}, img, padMove, orbit = padMove, move-orbit,
  move-orbit-rec), Tuples.seg (Tup, tsum, leT (⊑), AllLt (All<), tsum-mono,
  tsum-lt-eps0, dup-omega), Cascade.seg (Sc, valSc, ScAllLt, sucSc joinSc
  upSc zeroSc bumpSc with value and AllLt lemmas, omega-step, leSc (⊑Sc),
  scToTup, tupToSc), Rect.seg (pre, RD, rect, WD, rdOf, top0, topq, RDAllLt,
  leRD (⊑RD), rect-rdOf-ge, rect-arg-ge; sucTup, addNu (addν), sucRD, addRD,
  valSc-fold, rdOf-sucTup, rdOf-addNu, rect-addNu).  mx = maxN;
  RD 0 q = Tup q, so rdOf 0 = topq 0 = top0.  Graded-map operations kept as
  separate definitions (no record: different arities/widths).
  Unit notes: Σ and Π have eta (a lemma stated at (c, E) (a, t) applies at
  E t); `where` is allowed in a split branch; `Models[l].iterN` can be used
  qualified, without opening Models.
- Step 3b done (RectAlgebra, RectSum, RectApply, RectCurry, RectOrbitAct):
  RectAlgebra.seg (leSc-trans, leRD-trans, sucSc-ge, joinSc-left/right,
  zeroTup, zeroRD, taddTup, padd, joinRD(-left/-right), padTup, padRD,
  rect-padRD, flat0, flatRD, flatRD-ge, leInit (⊴), leInit-refl/-trans,
  le-lt-eps0, leInit-AllLt, pre-leInit, rect-leInit (rect-⊴), sucTup-AllLt,
  sucRD-AllLt, addTupc, addRDc, rect-addNuc (rect-addνc); RectSum: sumRD,
  tsum-rect, sumRD-AllLt; all ..-AllLt), RectApply.seg (hdRD, valSc-hdRD,
  preRD, rect-preRD, Jsh, ssh, valSc-ssh(-step), ssh-AllLt, rdOf-zero-id,
  ssub-head, sh, rect-ssub, sh-AllLt), RectCurry.seg (cmb, cmb-leInit-left/
  -right, cmb-AllLt, tsum-cmb-fm (tsum-cmb-⋖), hdOf, hdOf-val, tupToRD0,
  rect-tupToRD0, tupToSc-scToTup, valSc-base, scurryD, valSc-scurry(-step),
  rdOf-zero-id', curryD, rect-curry(-step), ..-AllLt), RectOrbit.seg
  (orbEI, rorbitD, rtail-iter, rorbit-step, rorbit-act, ..-AllLt).
  On width 0 (RD 0 q = Tup q): zeroRD 0 = zeroTup, joinRD 0 = taddTup,
  padRD 0 = padTup, flatRD 0 = flat0, addRDc 0 = addTupc, sumRD 0 = tsum,
  preRD 0 = pre; tupToRD0 = identity, rect-tupToRD0 = refl,
  rdOf-zero-id / rdOf-zero-id' = leT-refl (kept as names).
  Unit notes: Top has no eta (Id Top tt D is isTop tt D, not refl);
  RD n 0 does not reduce to Top for a variable n (Agda: it does), so
  hdOf (suc n) E = (E, zeroRD n 0) and every Agda definition whose first
  clause is "q = 0 for all p" splits on p first; `where` definitions may
  take parameters (it (i : Nat) .. in rorbit-step).  The big Agda `where`
  proofs became ..-step lemmas taking the induction hypothesis.
- Step 4 done (Predicate, SClause, IterClause, Fundamental): Predicate.seg
  (ord, wd, Dom, Dom-mono, Dom-sup, Dom-add (Dom-⊕), Dom-lt-eps0, Zero-/Succ-/
  Omega-clause, app-clause, K-clause), Clauses.seg (module SDatum[r,s,u]:
  m p q WF WG W2 n2 n3 De DF DG A1 A2 B B2 B3 dS, ..-AllLt, d1 d2,
  S-clause-at, S-clause; module IDatum[s]: p Wphi Wnu Wa n2 n3 DI DI2 DI3 dI
  dI-AllLt, dseq dseq-AllLt domseq, d1 d2, Iter-clause-at, Iter-clause),
  Bound.seg (TV, tap, tup-Zero .. tup-S, TupM : Model, DomR, DomR-ap,
  DR : Rel[MajM, TupM], fundamental, mu-lt-eps0 (μᵀ-<-ε₀),
  dialogue-tree-height-lt-eps0).  TupM values = (d : Tup (wd t)) * AllLt d;
  DR.R t x y = Dom t x y.1; Dom at arrows is the logical lifting up to
  currying the pair (e, AllLt e), so r-ap = app-clause by definition.  The
  widths of SClause/IterClause (WD .. of wd ..) agree with wd of the
  constant types definitionally, as in the Agda.  Agda's lambda+where
  clauses are ..-clause-at definitions with where (the two inductions of
  IterClause's where, dseq< and domseq, are module definitions).
  Theorem: dialogue-tree-height-lt-eps0 (e : Tm) (h : Has e FT)
  : Lt (height (tree e h)) eps0, for every typed e (Omega allowed).
  segc all: 27 modules, 0 failed; seg All.seg: 757 declarations, 0.12 s;
  max --opened 49 (RectOrbit.rorbit-step), new files max 34 (S-clause-at).
  Next: step 5 (sharpness, Theorems.seg).
- Step 5 done (Examples (repo), Sharpness, Main): Lower.seg (Agda Examples:
  I-free, leaf-term/query-term/iterated-term with ..-has ..-free, q0,
  leaf-tree query-tree iterated-tree (refl), leaf-height, query-height-le/ge,
  iota-generic(-zero) (ι-generic), iota-iter, iter-generic-le, one-add-num
  (one⊕ι), itj, iterated-height-ge/-le (base-le, iterated-step), tree-of,
  code-le-height, approximant, epsilon0, S-irrefl, no-term-of-height-eps0),
  Bracket.seg (Agda Cx/∋/Tm/abs/tm: data Cx, data Ex = var | con | app,
  Look, HasE (constants must be Has and OmegaFree), absVar, abs, abs-has,
  tm, tm-has, tm-free, arrs, lams, lams-has, close, close-has, close-free),
  Sharpness.seg (lmT, O (𝓞), alg; zerT sucT limT addT mulT oneT expT finT
  omegaT towerT towerTerm (tower-term), each with ..-has ..-free; zerD ..
  towerD (⟪ ⟫ = Eval[DM].ev) with refl lemmas zerD-eq .. towerD-eq; fold,
  mulC, expC, towerC, fold-id, fold-add (fold-⊕), mul-num-swap (⊗-ι-swap),
  mulC-num, mulC-omega, expC-wexp, towerC-tower; CRel (Rel), zerT-Rel ..
  towerT-Rel; P0 s0 l0 hz0 hs0 hl0, tree-towerTerm, tower-attained,
  tower-term-below-eps0, heights-cofinal, eps0-least), Theorems.seg (Agda
  Main: restated, no-SZ-le-Z, example, witness, tree-type, height-type,
  tower-base, tower-step, eps0-is-limit-of-tower, attained, cofinal, least,
  term-type; plus no-tower-bound).
  Deviations: the source syntax Ex is untyped with a typing HasE (no
  indexed families); app records the argument type, abs takes the body
  type.  Agda Examples.I is the existing Examples.I (K s s in the middle).
  Agda Rel -> CRel (name clash with SystemT.Rel).  The compiled terms are
  locked (`opaque zerT ; .. opaque expT ;`) right after their semantic
  equations ..D-eq (refl), and the CRel lemmas transport along them: this
  took Sharpness from 2.9 s (max opened 65, expD-eq 1.1 s) to 0.05 s
  (max 45).  attained also returns OmegaFree (towerTerm n); cofinal returns
  (e, h, OmegaFree e, bound); least quantifies over Omega-free terms only;
  restated / no-term-of-height-eps0 hold for every typed e.
  segc all: 31 modules, 0 failed, 0.27 s; seg All.seg: 972 declarations,
  0.30 s; max --opened 49 (RectOrbit.rorbit-step), new files max 45
  (Sharpness.expD-eq, tower-attained).
