# Handoff: making the Section 4 proof an ML1W proof (audit + Section 5 constructions)

State (2026-10-28): Section 4 is complete and green (`Top.seg`, Thm 4.41 `thm441c`/`thm441`,
no postulates; see `HANDOFF-TOP.md`). But Unit here is stronger than ML1W, so this is not
yet a proof that ML1W proves TI up to psi_{Omega_1} Omega_{I+n}.

Target (realistic): the Unit proof uses only principles of ML_{J,aux} (Setzer Section 3),
checked by audit. NOT a deep embedding of ML1W syntax (that is the known wall), so Lemma
3.8 (aux -> non-aux, a syntactic induction on derivations) and Cor. 4.42 (order type of OT,
semantics) stay informal/cited.

## The one missing principle

ML1W has one universe U (a la Tarski). Recursion may produce ELEMENTS of any type, incl.
codes in U and elements of N -> U (sets); it may NOT produce a TYPE by recursion outside U.
In these files: sets = level `l` (fine), classes = level `l+`. A `split` whose result is
`U lv` (or `Cl`) with lv the CLASS level is the offending pattern.

Grep (2026-10-28) of the Section 4 files:

    CA.seg:160  psiC : Bool -> U lv -> U lv -> U lv = split
    CA.seg:163  cin (a : T) (A : Cl) : T -> U lv = split        -- C^a(A)
    CA.seg:974  Sums (D : Cl) : T -> U lv = split
    WA.seg:120  Cor (A : Cl) : W1 A -> U wl = split              -- Cor^A
    Top.seg:126 WWi : N -> Cl = split                            -- WW_i
    OTLaws.seg:54 ifU (used by absurdB at class level)
    (GammaI.Str is at the set level: fine.)

These files are opened at the class level (`[ul+]`, `[gu+]`, `[tu+]`), where the
definitions above are recursion into types.

## Work items, in the order I would do them

1. **Read first (decides the risk): Setzer Remark 5.7 and Def. 3.14** (PDF page = printed
   - 112; Section 5 is printed pp. 152-155, Section 3 pp. 125-140; use page images, the
   OCR is bad). Setzer's Def. 5.6(c):
     Cor^A(t) := forall u : W_1^A. u <=' t -> (index(u) in M(A) and
                 forall v : tau^A(index(u)). index(pred(u)v) = v.0)
   needs a subtree relation u <=' t on W_1^A. The branching tau^A(x) is a CLASS-sized type
   when A is a class, so <=' is not obviously a recursion into U. Find how Setzer defines
   it (Def. 3.14 "index", "pred", the underlining rules for W in Remark 3.5/5.7). If it is a
   path/finite-sequence predicate, fine; if not, stop and discuss.
   Our Cor is defined by the recursion of Remark 5.7(c); after the change 5.7(c) becomes a
   lemma and wa-a / wa-b / cor-ind must use it.

2. **C^a(A) via K_a (Defs. 5.1-5.5, Remark 5.2), CA.seg.**
   - P^fin: finite sets as lists of T (no numeric coding needed); K_a(d) : list of lists,
     EXECUTABLE and level-free (put it in OT.seg style: no level in scope).
     Def. 5.3 (by recursion on d; use OUR head split of sums, not Setzer's last split):
       K_a(d) = {} if d or a not in OT; K_a(0) = K_a(I) = {{}};
       phi_b c, b + c: (K_a(b) (x) K_a(c)) u ({{d}} restricted to a);
       Omega_b: K_a(b) u ({{d}} restricted to a);
       psi_k c: (K_a(k) (x) K_a(c)) u ({{d}} restricted to a) if a <' k, else {{d}}.
     where M (x) N = {K u L | K in M, L in N}, "M restricted to a" = {K in M | K c a}.
   - C^a(A) := {y in OT | exists L in K_a(y). L c A}   (a formula: no recursion into types).
   - Remark 5.2 (exists over (x), over restriction) and Lemma 5.5 = our clauses
     ca-zero, ca-I, ca-plus, ca-phi, ca-om, ca-psi, ca-ok, ca-mk, ca-mono ... Prove them
     from the new definition; then downstream files should not change IF they use C only
     through these lemmas. CHECK FIRST: grep the `.opens` files for `cin` and `C ` (any
     declaration that opens C's definition must be rewritten).
   - Mirror: `tools/otsec4.py agree N` already compares C with CK (Setzer's K form).
     Re-target CK to the head-split K and run it before formalising.
   - psiC and Sums disappear or become list predicates.

3. **WW_i without recursion into classes, Top.seg.** Replace `WWi : N -> Cl` by a step lemma
   for an arbitrary class A and cardinal k = Omega_{I+j}:
     E(A, k), F(A, k)  =>  E(B, k+), F(B, k+)   with B = W(A) n k+,
   plus the base (A = WW n I, k = I). Thm 4.41 for each concrete n (0, 1, 2, 3 as
   declarations) by iterating the step: this is Setzer's meta induction. Keep the internal
   version too, labelled as using a universe above the classes.

4. **ifU / absurdB at class level.** Replace by: transport along Id Bool false true into a
   U-small family (code of the empty set), then empty elimination into any type. Small.

5. **Audit.**
   - Unit's Id: confirm it gives no more than J (no function extensionality, no K, no
     cubical extras) in what these files use. Look at core Base.seg / the checker's rules.
   - Data types at class level (`Or`, `W1`, Sigma, Pi): allowed (types formed from types).
   - Levels: only set level + class level; nothing at class level + 1 except the labelled
     internal-n variant. Make a grep/lint script in tools/ and record its output in README.
   - Cumulativity / `Lf`: corresponds to Setzer's underlining (aux theories); note it.

## Conventions (unchanged)

Every file: `seg/WRITING.md` (informal proof in the header first, one name per notion,
`.opens` per declaration). Mirror in `tools/` before formalising. Check with

    SEGD=~/CANONICITY/seg/headlinear/dist-newstyle/build/aarch64-osx/ghc-9.6.7/segd-0.1.0.0/x/segd/build/segd/segd
    timeout 60 $SEGD F.seg --opens F.opens

Changing CA.seg / WA.seg forces re-checking every later file (CA, WA, Clos, Lem417, Ag, WW,
GammaI, Top) with `--opens`; `.opens` lines that mention `cin`, `Cor` will change.
Checker gotchas: see HANDOFF-WW.md, HANDOFF-GAMMA.md (module names hide classes: write
`WW[l].WW`, `WA[l+].WA`, `Ag[l+].Ag`; never reuse an imported level name; check new names
against imports, shadowing is silent).

## Estimate

Items 2-5: about a week of sessions (item 2 ~500 lines). Item 1 is the risk: settle it
before investing in the rest.
