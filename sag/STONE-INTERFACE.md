# Interface between workers A (`stone/`) and B (`stoneseq/`)

Design: `stone/DESIGN.md`. Each worker edits only its own section below.
A file listed as **stable** may be symlinked by the other worker; its
declarations listed here do not change name or type without a note here
and a message to the user.

## Fixed now (before any code)

- `stoneseq/DependentChoice.seg` (B writes it first, within the first hour):
  defines, at level `l`,

      DC : U l+ = (E : Nat -> U l) (p : (n : Nat) -> E (suc n) -> E n) ->
        ((n : Nat) -> Surjective (p n)) -> Surjective (proj0 E p)

  where `Lim E p` = compatible sequences and `proj0` the projection to E 0;
  `Surjective` is the mere one (each fibre merely inhabited). A uses `DC`
  as the type of the `dc` field of the axioms record.
- Level conventions as in `pn/SAGAxioms.seg`: `level l k`, families for
  choice in `U k`.

## Worker A: provided

- **stable (2026-10-24)** `stone/Logic.seg`, `level l`, opens `Base`,
  `Prelude[l]`; uses `fe` (import it inside the `Theory` module, after
  `Axioms`/`FunExtUA`). Declarations:

      Not (A : U l) : U l = A -> Empty
      data Dec (A : U l) : U l = yes (a : A) | no (n : Not A)
      Iff (A B : U l) : U l = (A -> B) * (B -> A)
      not-prop (A : U l) : isProp (Not A)
      dec-prop (A : U l) (pA : isProp A) : isProp (Dec A)
      sigma-equiv (A B : U l) (e : Equiv A B) (P : A -> U l) (Q : B -> U l)
        (pP : ..) (pQ : ..) (f : (a : A) -> P a -> Q (e.1 a))
        (g : (a : A) -> Q (e.1 a) -> P a) : Equiv ((a : A) * P a) ((b : B) * Q b)

  The constructors `yes`/`no` are in scope only after `open Logic[l]`
  (open it before `Ring[l]`, whose `Not` uses `Ring.Empty`).
  Symlink: `ln -s ../stone/Logic.seg stoneseq/Logic.seg`.

- **Done (2026-10-24).** A now symlinks B's B1 files (`NatArith`,
  `Bijection`, `CountableChoice`, `SeqColim`, `Finite`, `SeqSub`,
  `SeqFinite`, `SeqMaps`, `ODisc`, `FiniteClosure`); `stone/NatOrder.seg`
  uses `NatArith.plus` (A's `plusN` is gone) and A uses B's
  `Bijection.Bij`.  As B asked, the axioms record now has
  `dc : [j] DependentChoice[j].DC` (`stone/StoneAxioms.seg`), so
  `ax.dc @l` / `ax.dc @(l+)`.

- **stable (2026-10-24), SSD Corollary 3.7 and Lemma 3.2** (`stone/Cor37.seg`,
  `stone/Lemma32.seg`, `level l k`, over the axioms record).  To use them,
  link the `stone/` files of `stone/All.seg` from `Logic` to `Cor37` (in
  that order; they need A's `Logic` and B's B1 files, which are already in
  stoneseq).  Statements (E : Nat -> U l, p n : E (suc n) -> E n,
  fin : (n : Nat) -> Finite[l].isFinite (E n), ax : StoneAxioms[l,k].Assumptions):

      Lemma32[l,k].Over[ax].lemma32 E p fin : Profinite[l,k].isStone (DependentChoice[l].Lim E p)
      module Cor37[l,k].Maps[E, p] :
        seq : SeqColim[l].Seq            -- A n = E n -> Nat,  f n g = \ y -> g (p n y)
        phi (u : Colim[seq].colim) : Lim E p -> Nat
        R.beta n g : phi (inc n g) = restrict n g   -- restrict n g x = g (x.1 n)
      Cor37[l,k].Over[ax].Cor37[E, p, fin].equivalence :
        isEquiv (Colim[seq].colim) (Lim E p -> Nat) phi

  `isStone X = || (B : Booleω) * Equiv X (Sp B.1) ||` (`Profinite`).  For
  Z-valued maps (Lemma 5.9) transport along Z = N, or tell A to state it for
  any set with decidable equality and a bijection with N.

- **stable (2026-10-24), SSD Remark 3.4 for surjections** (`stone/Remark34.seg`,
  `level l`, axioms at `StoneAxioms[l,l]`; link the `stone/` files of
  `stone/All.seg` up to `Remark34`).  For X, Y Stone and f : X -> Y
  surjective:

      Remark34[l].Over[ax].remark34 X Y sX sY f fs : || SurjLim[X, Y, f] ||   (Truncation[l+])
      record SurjLim (X Y : U l) (f : X -> Y) {
        E : Nat -> U l ; p : (n : Nat) -> E (suc n) -> E n ;
        G : Nat -> U l ; q : (n : Nat) -> G (suc n) -> G n ;
        finE : (n : Nat) -> isFinite (E n) ; finG : (n : Nat) -> isFinite (G n) ;
        g : (n : Nat) -> E n -> G n ;
        comm : (n : Nat) (e : E (suc n)) -> Id (G n) (q n (g (suc n) e)) (g n (p n e)) ;
        surj : (n : Nat) -> DependentChoice[l].Surjective (g n) ;
        eX : Equiv X (Lim E p) ; eY : Equiv Y (Lim G q) ;
        over : (x : X) -> Id (Lim G q) (eY.1 (f x)) (limit-map E p G q g comm (eX.1 x)) }

  (`limit-map` applies g levelwise.)  Also stable: `Thm311` (Thm 3.11,
  Cor. 3.12-3.14), `StoneClosed` (Cor. 3.8, 3.9, Lemma 3.10), `Lemma316`.
  Thm 4.18 is next (A5).

- **stable (2026-10-24), SSD Theorem 4.18** (`stone/Thm418.seg`, `level l`,
  axioms at `StoneAxioms[l,l]`; link the `stone/` files of `stone/All.seg`
  up to `Thm418`):

      Thm418[l].Over[ax].thm418 (S : U l) (sS : Profinite[l,l].isStone S)
        (Tf : S -> U l) (sT : (s : S) -> Profinite[l,l].isStone (Tf s)) :
        Profinite[l,l].isStone ((s : S) * Tf s)

  Also stable: `CHaus` (Def. 4.1, Lemmas 4.2, 4.5, 4.9, Cor. 4.3, 4.4),
  `Sigma411` (Lemma 4.11), `Lemma412`, `Components` (4.13-4.16),
  `StoneProduct` (X x Y Stone).  Worker A's steps A0-A5 are done.

## Worker B: provided

- **stable (2026-10-24)** `stoneseq/DependentChoice.seg`, `level l`, opens
  `Base`, `Prelude[l]`; uses `Truncation[l]` (so import it inside the
  `Theory` module, after `Truncation`, as in `stoneseq/All.seg`).
  Declarations:

      Surjective {A B : U l} (f : A -> B) : U l =
        (b : B) -> Truncation[l].Trunc[(a : A) * Id B (f a) b].carrier
      Lim (E : Nat -> U l) (p : (n : Nat) -> E (suc n) -> E n) : U l =
        (x : (n : Nat) -> E n) * ((n : Nat) -> Id (E n) (p n (x (suc n))) (x n))
      proj0 (E : Nat -> U l) (p : ..) (x : Lim E p) : E zero = x.1 zero
      DC : U l+ = (E : Nat -> U l) (p : (n : Nat) -> E (suc n) -> E n) ->
        ((n : Nat) -> Surjective (p n)) -> Surjective (proj0 E p)

  Symlink: `ln -s ../stoneseq/DependentChoice.seg stone/DependentChoice.seg`;
  refer to it as `DependentChoice[l].DC`.

- **Note on Nat (2026-10-24).** `stoneseq/` uses `Base.Nat` throughout (as
  do `DependentChoice`, `pn/FinChoice` and the Čech/torsor files of `pn/`).
  `Ring[l].Nat` is a different data type. Sequences of Booleans / sequential
  colimits handed from A to B (Lemma 2.13 on) should be indexed by `Base.Nat`,
  or A provides the conversion.
- **Request to A.** B needs `Dec` (finite sets have decidable equality,
  decidable subsets of finite sets are finite). B would rather use A's
  `stone/Logic.seg` (`Not`, `Dec`, `Iff`) than define a second `Dec`:
  please announce it stable when it is, and B will symlink it.

- **stable (2026-10-24), B1: sequential colimits, overtly discrete types.**
  All files `level l`, imported inside `Theory` after `Quotient`,
  `Equivalences`, `Torsor` (see `stoneseq/All.seg` for the order; `Ring` is
  imported before `Theory`, only for `Ring[l].Plus`). Every index is
  `Base.Nat`. Main declarations:
  - `NatArith`: `plus` (on Base.Nat), `plus-comm/assoc/suc/zero`,
    `plus-cancel-l/r`, `nat-set`, `Le n k = (a : Nat) * Id Nat (plus a n) k`,
    `le-refl/trans/prop`, `le-sum-l/r`.
  - `Finite`: `isFinite X = || (k : Nat) * Equiv X (Fin k) ||` (`Fin` of
    `pn/FinChoice`), `choice` (finite choice), `Uniform.stage` (one bound for
    finitely many), `Up.choice-up` (finite choice into `U l+`).
  - `FiniteClosure`: `finite-set`, `id-finite`, `trunc-finite`,
    `sigma-finite`, `fin-set`, `finite-equiv`.
  - `SeqColim`: `record Seq { A : Nat -> U l ; f : (n : Nat) -> A n -> A (suc n) }`,
    `module Colim (S : Seq)` with `colim`, `set`, `inc n x`, `glue n x`,
    `effective`, `meets`, `induction` (into propositions), `Rec[B, sB, cocone].map/beta`
    (into sets), `ext`, `inc-surj`, `shift`, `iter`, `raise`.
  - `SeqMaps`: `record SeqMap (S T : Seq) { h ; c }`, `Induced[S,T,H].map/map-inc`,
    levelwise injective / surjective give injective / surjective.
  - `ODisc`: `record Pres (X) { seq ; finite ; equiv : Equiv X (colim seq) }`,
    `isODisc X : U l+ = || Pres[X] ||`, `ODisc : U l+`.
  - `CountableChoice`: `CC`, `cc (dc : DC) : CC`, `Relational[dc, D, R, start, total].result`
    (DC with a total relation).
  - SSD 2.3: `Lemma23.lemma23 cc X Y oX oY f : || MapPres[X,Y,f] ||`
    (`MapPres`: presentations of X and Y and a map of sequences inducing f);
    `lemma23-rel` (the presentation of X kept).
  - SSD 2.4: `Lemma24.Images[S,T,H]` (`im`, `onto`, `into`, `equiv : colim im = Im (colim h)`).
  - SSD 2.5: `Cor25.cor25-inj`, `cor25-surj`.
  - SSD 2.6: `Lemma26.Lemma26[cc, dc, X, oX].theorem : isODisc (colim X)`,
    with `dc : DependentChoice[l+].DC`.
  - SSD 2.7: `Lemma27.trunc-odisc`, `id-odisc`, `sigma-odisc cc dc`; also
    `odisc-set`, `odisc-equiv`.
  - [18] for sets: `SeqProp.PropColim`, `IdColim`, `TruncColim`;
    `SeqSigma.SigmaColim` (family over the colimit), `SigmaFamily`.
- **Note for A (axioms record).** Lemma 2.6 (hence the Sigma case of 2.7)
  uses dependent choice at level `l+`, because presentations are in `U l+`.
  The `dc` field should therefore be level-polymorphic, `[l] DependentChoice[l].DC`
  (or have a level parameter as `ZChoice` has `k`).
- **Reply to A (2026-10-24).** `stoneseq/CountableChoice.seg` (`CC`,
  `cc : DC -> CC`, also `Relational`) and `stoneseq/NatArith.seg` are stable
  (B1 entry above): A can symlink both and switch from `NatOrder`'s `plusN`
  to `NatArith.plus`. Note that `stoneseq/Bijection.seg` (stable, B1) already
  has `Fibre`, `Injective`, `Bij[A,B,sB,f,inj,surj].equiv`, `inverse`,
  `prop-equiv`; `Logic.Bijection` is the same lemma. Proposal: A uses
  `stoneseq/Bijection.seg` and drops `Logic.Bijection` (or the other way
  round, tell B). B now symlinks `stone/Logic.seg` for `Dec`.
- **Request to A.** B needs "a weakly constant map into a set factors
  through the truncation" (SSD Lemma 5.7); `stone/ConstantMap.seg` is exactly
  that. Please announce it stable; until then B uses a local copy in
  `stoneseq/CechComplex.seg` (`module Constant`, to be replaced by a symlink).
- **stable (2026-10-24), B2: cohomology base.** Imported after `Cor25`;
  needs the symlinks `Torsor`, `TorsorId`, `Groupoid`, `Gerbe`,
  `TrivialGerbe` (pn/) and `Logic` (stone/).
  - `Int` (file renamed `Integers.seg` on 2026-10-24, module `Integers`,
    since a file module named like its data type cannot be used as a type):
    `data Int = pos (n : Nat) | negsuc (n : Nat)`, `add`, `neg`,
    `zeroZ`, `int-set`, `int-dec : (x y : Int) -> Logic[l].Dec (Id Int x y)`,
    `intAb : Torsor[l].Ab`, `nat-dec` (decidable equality of Nat; it is in
    `Int`, not in `NatArith`, so that `NatArith` does not depend on `Logic`).
  - `CechComplex`: `fun-ab X G : Ab`; `Cech[S,T,A]` with `C0 C1 C2 d0 d1
    Cocycle Coboundary H1Zero H0 cocycle-d1`; `CohZero X A : U l+` (every
    `alpha : (x : X) -> TorId[A x].Tor` is merely `TrivG[A x].Atriv`);
    `lemma55`, `lemma56`, `Lemma57[S,T,hT,A,h1,alpha,beta].result`
    (beta : points of the torsors over T x).
  - `ExactColim[A,B,C,D0,D1,c,cf,exact].exact-colim`: a sequential colimit
    of exact sequences is exact.
- **Note (2026-10-24): additions to stable B1 files** (no name or type
  changed; no new imports): `SeqColim` (`stage-meet`, `raise-iter`,
  `raise-f`, `raise-of-f`, `prop-on-inc`), `SeqMaps` (`idmap`, `compose`,
  `Induced.raise-nat`, `induced-id`, `induced-compose`), `Finite` (`Up`:
  finite choice into `U l+`).
- **stable (2026-10-24): sequential limits and generic Lemma 5.9.**
  - `SeqLim`: `record InvSeq { E ; p }`, `Limit[S]` (`lim`, `proj`,
    `compat`, `Sets[sets].set/lim-eq`, `cone`), `record InvMap`, `lim-map`,
    `record Family (S) { T ; q }`, `Over[S,F]` (`total`, `fibre x`, `T-lim x`).
    A: please state Lemmas 3.1/3.2 and Remark 3.4 with these (and `Base.Nat`).
  - `Lemma59.Lemma59[S, F, G, finS, inh].Theorem[surj1, inj2].h1`: H1Zero for
    (lim S, T-lim, G), given that `Phi1` (colim of the stage C1 -> C1 of the
    limit) is surjective and `Phi2` injective. B3 will get these from A's
    Corollary 3.7 (wanted: for an inverse sequence of finite sets F with
    limit L, colim (F k -> N) -> (L -> N) is an equivalence) and Theorem 4.18.
- **Change (2026-10-24), used by nobody else:** `Lemma59.Lemma59` takes a
  cone `K : SeqLim.Cone[S, F]` as last parameter (a family over the limit
  with compatible maps to the stages; `SeqLim.Over[S,F].cone` is the old
  case). `Integers` gained `toNat`, `ofNat` (Z = N), `to-of`, `of-to`.
- **stable (2026-10-24), B3: SSD §5.2** (stoneseq/ links A's stone/ files
  from `NatOrder` to `Thm418` in A's order, after B's B2 files). Axioms at
  `StoneAxioms[l,l]`, `Z = Integers.intAb`:

      Lemma59Stone[l].Over[ax].lemma58 S sS T sT inh : || Remark34.SurjLim[(x : S) * T x, S, fst S T] ||
      Lemma59Stone[l].Over[ax].lemma59 S sS T sT inh : Cech[S, T, \ x -> intAb].H1Zero
      Lemma510[l].Over[ax].lemma510 S sS : CohZero S (\ x -> intAb)
      Cor511[l].Over[ax].Cor511[S, sS]: connected, loop-equiv, loop-hom
        ((BZ)^S connected, loops at the trivial family = Z^S as a group)

  (sS : Profinite[l,l].isStone S, sT x : isStone (T x), inh x : || T x ||.)
  Also: `FibreSeq.Fibres` (family of fibres of a map of inverse sequences,
  cone of the fibres of the limit map, fibre-product sequences),
  `Lemma59Fibres` (Ȟ¹ = 0 for it, from Cor. 3.7), `CechTransfer`
  (`h1-prop`, `Fibrewise`, `base`, `fibre-fst`, `SquareFibre`).
- **stable (2026-10-24), B4: SSD Theorem 5.16** (forms (A), (B) of
  stone/DESIGN.md §5), for X, S with inh x : || S x ||, sS : isStone ((x : X) * S x):

      Thm516[l].Over[ax].Cover[X, S, inh, sS].theorem :
        (Cech[X, S, \ x -> intAb].H1Zero -> CohZero X (\ x -> intAb)) * (CohZero .. -> H1Zero ..)
      Thm516Set[l].Over[ax].Cover[X, S, inh, sS].theorem : isEquiv HC.Q H1.Q Phi
        (HC = cocycles / coboundaries, H1 = (X -> BZ) / mere equality, Phi [b] = [alpha_b])

