# Worker A: Boolean layer, SSD §1, then §2.2–4.3

Read first: `stone/DESIGN.md` (rules, representation choices),
`../STONE-INTERFACE.md`, the paper `SSD.pdf` (repository root; its text can
be extracted with `pdftotext`), and for the style of the project
`seg/notes/sag.tex` §2–3 and `pn/SAGAxioms.seg`. You own `sag/stone/`
only. Worker B works in `sag/stoneseq/` at the same time.

## Steps

- **A0. Skeleton.** `stone/All.seg` like `exterior/All.seg` (symlinks to
  `../pn/` for the foundation: Base, Prelude, Paths, Axioms, FunExtUA,
  Replacement, Ring, Truncation, Quotient, Presentations, ...). Check that it
  loads: `./segc sag/stone changed` from the root.
- **A1. Boolean algebras.** Bool with decidable equality; Boolean algebras
  (record your choice in DESIGN.md §4); morphisms; the free algebra 2[I] for
  finite I with decidable equality; 2[N]; quotients by a sequence of
  relations; countably presented algebras, Booleω (SSD Def. 1.3, Remark 1.4);
  Sp(B) = Hom(B, 2) (Def. 1.7); Examples 1.6, 1.8 (2, trivial algebra,
  Cantor space, B∞ and N∞ with the normal form of elements of B∞);
  Lemma 1.9.
- **A2. Axioms.** `stone/StoneAxioms.seg`: record with `duality`, `formal`,
  `local`, `dc` (type `DC` from `stoneseq/DependentChoice.seg`, symlinked
  once B has written it). SSD §1.3: Remark 1.10 (Sp is an embedding,
  Hom(A,B) = (Sp B → Sp A)), Lemma 1.12, Corollary 1.13.
- **A3. SSD §1.4–1.6.** Theorem 1.14 (¬WLPO), Theorem 1.15, Corollary 1.16
  (MP), Theorem 1.17 (LLPO) and Lemma 1.18; open and closed propositions,
  Remark 1.20, Lemmas 1.21–1.24, Corollary 1.22.
- **A4. Join with B** (needs B's sequential colimits): SSD §2.2–2.3
  (Lemma 2.8, Lemma 2.12, Lemma 2.13, Corollary 2.14, Remarks 2.15–2.16),
  §3 (Lemmas 3.1–3.6, Corollary 3.7, §3.2, Theorem 3.11, Corollaries
  3.12–3.14, Lemma 3.16). Announce Remark 3.4, Corollary 3.7 and Theorem 3.11
  as stable in the interface: B needs them for SSD §5.2.
- **A5.** SSD §4.1–4.3, up to Theorem 4.18. Announce Theorem 4.18 as stable.

Done when each step checks under `./segc sag/stone changed`, every file < 10 s,
and DESIGN.md "Status" lists what is proved, with SSD numbering.

## Status (2026-10-24)

All steps A0-A5 done (see DESIGN.md §6 for the list with SSD numbering):
SSD §1; §2.2-§3 (Lemma 2.8; Lemmas 3.1, 3.2, 3.5, 3.6, Cor. 3.3 (binary),
3.7-3.10, 3.12-3.14, Theorem 3.11, Lemma 3.16, Remark 3.4 for surjections);
§4.1-4.3 up to Theorem 4.18.  Announced stable to B: Logic, Cor. 3.7,
Lemma 3.2, Remark 3.4, Thm 3.11 and the §3.2 results, Theorem 4.18.
Whole directory: 3264 declarations, 0 failed, 0.99 s (`segd All.seg`).

Not done (listed in DESIGN.md §6): Lemmas 2.12, 2.13, Cor. 2.14, Remarks
2.15, 2.16 (bypassed), Remark 3.4 for general maps / injections, Cor. 3.3
beyond binary products, Remark 3.15, Lemma 4.10 (converse), Cor. 4.6, 4.7,
Remark 4.8.  Cleanup to do: the bits of a point of a presented spectrum
(`bits`, `bits-zeros`, `point-of`) are stated in ImageClosed, Thm311,
Lemma316, Compact, and once generically in `StoneProduct.Bits`: move
`Bits` early and use it everywhere (rule 2).

## --opened (WRITING.md rule 6), measured 2026-10-24

Every file checks in < 0.2 s, but these declarations open more than ~500
definitions (whole-run `--opened`):

    2063 ProductPresented.PP.preimage       1478 LLPO.f-injective
    1052 Remark110.Two.surjective            937 Presented.hom-ext-gen
     776 ProductPresented.PP.Factor.kills-kernel-at
     772 NoRetraction.below    745 Product.fibre-at   740 BinfFacts.subst-lemma
     719 NoRetraction.above    704 LLPO.llpo-case     703 FreeFinite.Into.unique
     694 PP.psi-shift   693 NoRetraction.uv   683 PP.kills-odd/kills-even
     672 FreeCountable.ev-inj  578 LLPO.kernel  535 Presented.sp-value
     516/500 PP.Factor.agree-right/left  510 PP.psi-ne
    1040 Cor37.Setting.vanish-ideal   965 Lemma412...kernel-elem
     838 StoneProduct...injective     (same mkBA/mkCRing pattern)

What they open: the Boolean algebras built with `mkBA`/`mkCRing`
(`FreeCountable.free`, `QuotientBA.quotient`, `Product.product`,
`two`): `X.ring.R`, `X.ring.add` are decoded to `Elem`, `eadd`, pairs,
quotient carriers, about 250 times in the worst case.  NOT FIXED YET.  One
attempt (writing `preimage` with the projection names `FN.free.ring.add`,
`D.product.ring.add` that the morphism laws use) made it worse (342
decodings instead of 254), so the remedy needs a diagnosis first: which
comparisons decode (trace), then accessor / "by definition" refl lemmas
next to `mkBA` in `BooleanRing`, `QuotientBA`, `Product`, `FreeCountable`
(rules 3, 5), and morphism-law accessors instead of `h.2.2.1` chains.
Diagnosis (canonicity-69, 2026-10-24): no single comparison is expensive
(SEG_TRACE, threshold 1000); `mkCRing`/`mkBA` are the resolver's generated
constructors (`mkX fields = new X[fields]`), which a reader treats as
constructors; a checker change is proposed for them.  The rest (product,
quotient, free algebra by definition) is legitimate where the text uses the
definition; otherwise add refl lemmas next to the construction (e.g.
`Prod.add-def`).  Existing cheap declarations stay as they are; new files:
informal proof first, one name per notion, `--opened` after each file.

## Gaps

Statements of the paper used without proof, citations replaced by proofs,
and changes of route:

1. **Remark 1.4** (any countably presented algebra is merely of the form
   2[N]/(r n)): Booleω is *defined* in this form; the reduction from
   Def. 1.3 (countable I, J) is not formalised.
2. **Example 1.8 (iv)**: B∞ is presented by g n /\ (g 0 \/ .. \/ g (n-1))
   (indexed by N, no pairing N -> N x N) instead of g m /\ g n for m /= n;
   the two generate the same ideal (comment in `Examples`, not formalised,
   not needed: N∞ is Sp of this presentation).  The normal form
   (every element is \/ g i or /\ not g i) is **not used**: 1.17 and 1.18
   are proved with the standard points delta i and 0 (`BinfFacts.std-ideal`:
   an element vanishing at all of them is in the ideal).
3. **Lemma 1.12**: the paper uses that Sp is an embedding and that the
   trivial algebra has empty spectrum; replaced by: if Sp(B) is empty, the
   evaluations of 0 and 1 are equal, and evaluation is injective (Axiom 1).
4. **Corollary 1.13** applies Axiom 2 to 2 -> B, so needs 2 : Booleω,
   used silently; proved (`TwoPresented`: 2 = 2[N]/(g n)).
5. **Theorem 1.14** needs 2[N] : Booleω (presented by zero relations).
6. **Theorem 1.15 / Corollary 1.16**: "2/(alpha n)" must be in Booleω for
   Lemma 1.12; used silently.  We use 2[N]/(g n \/ alpha n) instead.  The
   paper's proof of 1.15 uses that alpha hits 1 at most once; ours finds the
   least n with alpha n = 1 for any alpha (a proposition, so obtainable from
   the mere k with J k = 1), which is MP directly; 1.15 is an instance.
7. **Theorem 1.17**: "f is a well-defined morphism in Booleω" needs
   B∞ x B∞ : Booleω, and the proof needs Sp(B∞ x B∞) = N∞ + N∞; both used
   without proof.  Proved: Booleω is closed under binary products
   (`ProductPresented`, injectivity by Axiom 1) and Sp(A x B) = Sp A + Sp B
   (`Product`).  Injectivity of f via standard points (item 2).
8. **Def. 1.19** writes alpha n = 0 for open propositions; Lemma 2.8 and
   Corollary 1.16 use alpha n = 1, which we follow (equivalent by negation).
9. **Lemma 1.21**: the "known fact" that LLPO is equivalent to
   not (P /\ Q) <-> not P \/ not Q for open P, Q (citation) is replaced by a
   direct proof of "closed propositions are closed under finite
   disjunction" from LLPO (first hit of the interleaving, `OpenClosed.ClosedOr`).
   The surjection N ->> N x N is replaced by joins over squares
   (`BoolSeq.sq`).  Countable choice is a hypothesis (`Countable[cc]`); it
   follows from Axiom 4 (B's `CountableChoice.cc`).
10. **Remark 1.10**: the citations of [4] (Lemma 3.1.2, Prop. 2.2.1) are
    replaced by a direct proof of Hom(A, B) = (Sp B -> Sp A) from Axiom 1
    (`Remark110`).  "Sp is an embedding Booleω -> U" and the dual
    equivalence of categories (HoTT book Lemma 9.4.5) are not formalised.
11. **Remark 1.11**: not formalised.
12. **Lemma 3.2** ("by Remark 1.10 and Lemma 2.6, Stone is closed under
    sequential limits, and finite sets are Stone"): proved directly by a
    coding of lim E in Cantor space (`LimCode`, `Lemma32`), using countable
    choice for enumerations of the E n.
13. **Lemmas 3.5, 3.6** are proved inside the proof of **Corollary 3.7**
    (`Cor37`), for an arbitrary sequence of finite sets; Lemma 3.5's
    "Hom(2^k, _) commutes with sequential colimits" is replaced by: each of
    the finitely many fibres {f = j} is an element of B with a truth table,
    which reads only finitely many blocks.  The paper's 3.5 uses Remark 1.10
    and a colimit of Boolean algebras that is not constructed there.
14. **Theorem 3.11 (iv) -> (ii)**: the paper uses Remark 2.15 (the kernel
    of a map in Booleω is enumerable); replaced by: y is in the image iff
    2[N]/(rX, coordinates - y) is nontrivial, which by Lemma 1.12 and
    Cor. 1.13 is the countable conjunction "J K /= 1" of decidable
    conditions (`ImageClosed`).  (v) -> (iv) uses local choice as in the
    paper (Remark 1.11 is used in this form, not proved separately).
15. **Remark 3.4** (no proof in the paper beyond "by Remark 2.16 and
    Axiom 2"): proved for surjections only (`Remark34`), by presenting X
    with the coordinates of f as even bits and taking the images of the
    stages under masking; Axiom 2 is not needed.  The cases of arbitrary
    maps and of injections are not formalised.
16. **Lemma 4.5** is proved through a lemma not in the paper: a cover of a
    Stone space by countably many decidable subsets has a finite subcover
    (`Compact`); the reduction from closed subsets uses MP and a pairing.
17. **Lemma 4.11** needs X x 2^N Stone for X Stone (Cor. 3.3 for products,
    not proved in the paper; `StoneProduct`).
18. **Lemma 4.12**: the paper's route (open subalgebra of 2^S, hence overtly
    discrete by Lemmas 2.8, 2.7, hence countably presented by Cor. 2.14) is
    replaced by a direct presentation: generators enumerated with open
    witnesses, relations = the enumerated elements whose image is below some
    J K (`Lemma412`).  Cor. 2.14 and Lemma 2.12 are therefore not used.
19. **Lemma 4.17** uses "every point of 2^S, S Stone, is an evaluation",
    from Axiom 1 (not stated in the paper).
