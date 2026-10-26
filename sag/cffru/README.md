# cffru/: the univalent sharpening of cffr (HANDOFF-CFFR-UNIVALENT.md)

A layer over `../cffr/` (all its files linked read-only, plus `pn/ModuleSIP` and the generic SIP `../sip/{SipGeneric,AbAxioms,ModuleSIP2}`; for WiebeFree also
`../wiebe/` and `exterior/` ExteriorRelation, Naturality, CharPoly, DeterminantTrick, read-only).
Check: `./segc sag/cffru all` from the `unit` root (cold: 252 modules, 0 failed,
about 7.5 s; the step-2 files Dictionary .. Natural together under 1 s).
Ring `D : TrueGrade.RD`; modules `Modules.Over[D.1,D.2].Module` = Alg73 modules
over `RingBridge.Over[D.1,D.2].ring` (the bridge of the two ring records).

| sharpened statement | declaration | Gaps entry removed |
|---|---|---|
| R^n as a module, matrices of linear maps, f x = apply (mat f) x | `FreeModules.Free`, `mat`, `apply-mat` | — |
| composite zero / exact / injective for linear maps = cffr's matrix notions | `FreeModules.compose-zero`, `exact`, `injective` | — |
| R^n ~ R gives n = 1 or 1 = 0; R^1 ~ R is v ↦ v_1 w, w a unit | `FreeModules.rank-one`, `UnitLine` | — |
| finite free resolution of an ideal, basis-free | `FreeResolution.FFRes`, `ResOf`, `Bases` | — |
| transport lemma (structure identity + funext) | `FreeResolution.Transport.free-transport` | — |
| a gcd depends only on the ideal | `GcdIdeal.Same.Gcd.result`, `Same.vanish` | — |
| **Thm 8.9, paper form**: a finite free resolution of (a_0..a_n) gives merely a gcd, regular unless all a_j = 0 | `Thm89U.Over.Theorem.theorem89` | "Thm 8.9 is stated for the 1 x 1 minors of the last map" (now: any ideal, any resolution, last map's image = the ideal) |
| **Cor 8.10, paper form**: every (a, b) has a finite free resolution ⇒ every a, b merely have a gcd (cffr's `Thm89.GcdOf`) | `Thm89U.Over.Cor810.cor810` | the FFR encoding (last map with exactly a, b as nonzero entries) |
| **step 3**: regular gcds of (a_K) form a set with a free, transitive action of R^x; an R^x-torsor when merely inhabited | `GcdTorsor.Over.At.RegGcd`, `act`, `torsor` | — |
| the gcd ideal without choosing a gcd; equal to (g) for every gcd g | `GcdTorsor.Over.At.InGcd`, `Principal.to/from` | — |
| **Cor 8.10 sharpened**: a, b not both 0 ⇒ their regular gcds form an R^x-torsor; for all a, b the gcd ideal is merely principal | `GcdTorsor.Cor.torsor`, `Cor.principal` | "merely have a gcd" → canonical torsor / ideal |
| uniqueness of the second factor: x regular of degree p, x_I y = x_I y' for |I| = p ⇒ y = y' | `Factorisations.Over.Unique.result` | — |
| **Lemma 8.4, contractible**: for β fixed, the γ with ∧^q(B) = γ bhat^T form a contractible type | `Factorisations.Over.Contr84.contractible` | — |
| **Cor 8.5, contractible**: the normalised chains (α_0 = 1, α_(t+1) = unstar β_t, ∧^(rk t)(M t) = β_t α_t^T) form a contractible type, centred at cffr's construction | `Factorisations.Over.Chain.Res.contractible`, `center`, `chain-prop` | — |
| **Thm 8.7**: the last factor and the Cayley determinant are the same for every chain | `Factorisations.Over.Chain.Res.Det.gamma-unique`, `det-unique` | — |
| module structure identity as an equivalence: Id Mod A B ≃ LinEquiv A B; Mod locally small (the generic SIP of `../sip`, linked: `SipGeneric`, `AbAxioms`, `ModuleSIP2`; `FreeModules.MS` is `ModuleSIP2`) | `ModuleSIP2.Over.sip-equiv`, `pth`, `local-small` | — |
| the small type FF : U l of finite free modules (replacement: image of n ↦ R^n), its induction into propositions | `FiniteFree.Over.FF`, `ff-ind`, `ff-finite`, `finite-ff` | — |
| ∧M of a finite free module (no basis): the contractible type of exterior algebras of M; ∧f; functoriality | `ExteriorFree.Over.contractible`, `Lam`, `Wedge.wedge`, `wedge-gen`, `Functor.wedge-id`, `Compose.wedge-comp` | — |
| degree k in ∧M without a basis (for every basis, the coordinates have degree k); ∧f preserves degrees | `ExteriorDegreeM.Over.Deg`, `Preserve.result`, `phi-degree` | — |
| ∧^k M as a module, ∧^k f; the top line ∧^n M is a line | `TopLine.Over.Piece`, `PieceMap.map`, `Top.line` | — |
| the module Hom(K, M); Hom of two lines is a line | `Lines.Over.Hom.hmod`, `hom-line` | — |
| coordinate dictionary D: (*) in coordinates, Λ(B)(x) = top(x ∧ β) γ for x of degree q, is equivalent to cffr's B_K = bhat_K γ (bhat = unstar β); top(x ∧ y) = dot(x, unstar y) | `Dictionary.Over.Stage.to-wedge`, `from-wedge`, `top-pair` | — |
| Lemma 8.4, every stage of a normalised chain, and the last factor are (*); with Thm 8.7, Λ(M_last)(x) = top(x ∧ β_T) det ω | `Dictionary.Over.At84.wedge`, `Chain.Res.stage-wedge`, `Chain.Res.Last.last-wedge`, `Last.Det.det-wedge` | "unstar(beta) = ±beta*": (*) never compares with β* |
| (*) for finite free modules without bases: R_k = Hom(K, ∧^(q+p) P), x ∧ a' in R_k, ∧^q f (x) = a(x ∧ a'); a map is regular when no nonzero scalar kills its image (BE's I(a) with zero annihilator) | `StageStar.Over.RkOf`, `Stage.wedge-with`, `Stage.Star`, `RegularMap` | — |
| with bases, (*) is D's Wedge and regularity is regularity of the coefficients | `StageStar.Over.Stage.Coords.At.to-coords`, `from-coords`, `Coords.reg-to`, `reg-from` | — |
| **T1**: (*) determines a_k when a_(k+1) is regular | `StageStar.Over.Stage.Bases.unique`, `solution-prop` | — |
| **T2, BE Thm 3.1 without bases**: on a complex of finite free modules (cffr's hypotheses for every choice of bases) the structures (a_t), R_0 = R, a_0 = 1, R_(t+1) = Hom(R_t, ∧^(top) G (t+1)), form a contractible type | `Structure.Over.Chain.Res.contractible`, `structure-prop`, `Center.center` | — |
| **T3, Thm 8.7 with the line**: Det(F) = R_(T+1) is a line, a_Det : Det(F) → ∧^(r_1) F_0 is canonical; for bases, to(a_Det(ρ)) = det ω with det cffr's Cayley determinant (a regular gcd); the image of a_Det is the gcd ideal of the r_1-minors | `DetLine.Over.Chain.Res.Det`, `det-line`, `aDet`, `Coordinates.value`, `gcd`, `regular`, `image-to`, `image-from` | "the Cayley determinant is the paper's up to sign": a_Det has no sign; det is its value at the basis element ρ fixed by the bases |
| **T4, naturality**: an isomorphism of complexes φ gives line isomorphisms e_t : R_t ≅ R'_t with a'_Det ∘ e = ∧φ ∘ a_Det | `Natural.Over.Chain.Res.eL`, `Natural.natural`, `Transfer.ST.star` | — |
| **D_k(f) without bases**: generators λ(f v_1 ∧ … ∧ f v_k) (v_t ∈ M, λ : ∧N → R linear); Gr ≥ 2 and regularity of this family | `DkFree.Over.Dk.Gen`, `value`, `GrTwo`, `Regular` | — |
| with bases, D_k(f) is the k-minors of the matrix: each minor is a generator, each generator is in the ideal of the minors; so Gr ≥ 2 / regularity hold for D_k(f) iff for the minors, and do not depend on the bases | `DkFree.Over.Dk.Coords.minor-value`, `value-in`, `to-free`, `from-free`, `reg-to-free`, `reg-from-free`, `Dk.change`, `reg-change` | "GradeHyp/RegHyp quantified over every choice of bases" (one choice now suffices) |
| Gr ≥ 2 passes to a family b when every a_i is in b's ideal (in the sense Gr ≥ 2 sees: `Within`), by unique choice | `DkFree.Over.Within`, `Transfer.result`, `reg-transfer` | — |
| **Thm 8.9 through Det(F)**: an FFRes of (a_j), with bases chosen merely, carries BE's structure on its own modules (hypotheses from exactness by Thm 6.8, for every choice of bases by DkFree); for last rank 1 the gcd of the a_j is a_Det at the basis element | `Thm89D.Over.FromBases.TH.Main.SR`, `gm`, `rg`, `Case.DT`, `Case.gcd-one`, `Thm89D.Over.theorem89` | "T2-T4 use Cor85's layout, not FFRes" |
| conjugation by bases preserves injective / composite zero / exact | `Thm89D.Over.Conj.injective`, `Conj3.zero`, `Conj3.exact` | — |
| stable of rank r without bases (∧^(r+1) f = 0, D_r(f) regular); the rank is unique unless 1 = 0; cffr's matrix stability gives it | `Ranks.Over.Rk.Stable`, `Rk.unique`, `Rk.Coords.from-matrix` | — |
| the free rank of a finite free module is unique unless 1 = 0 | `Ranks.Over.FreeRank.unique` | — |
| **rank data of an FFRes without choices** (R nontrivial): free ranks, ranks of the maps, BE's rank equations form a proposition, merely inhabited, hence an element | `DetFFR.Over.At.Data`, `data-prop`, `rdata` | — |
| **Det(F) of an FFRes without choices**: BE's structure on the resolution's own modules from the rank data; for last rank 1, Det(F) a line and the canonical a_Det | `DetFFR.Over.At.SR`, `gm`, `rg`, `Canonical.Det`, `det-line`, `aDet` | "Det(F) built under the truncation" |
| **Thm 8.7/8.9, ideal form**: the image of the canonical a_Det is the gcd ideal of the a_j | `DetFFR.Over.At.Canonical.image-to`, `image-from` | "image of a_Det = gcd ideal of the a_j not written" |
| ∧^k f = 0 gives D_k(A) = 0 for the matrix in any bases; D_r(f) regular gives D_r(A) regular (image form) | `Ranks.Over.Rk.Coords.vanish-minors`, `regular-image` | — |
| **last rank of an FFRes, without bases**: r m = 1 unless all a_j = 0 (r m = 0: ∧^1 T m = 0; r m ≥ 2: 1 = 0) | `DetFFR.Over.At.last-rank`, `LastZero.zero`, `LastBig.trivial`, `rank-one` | — |
| **Det(F) for every FFRes of a nonzero ideal** (R nontrivial) | `DetFFR.Over.At.NonZero.C` (= `Canonical[rank-one nz]`), `DetFFR.Over.OfRes` | "`Canonical` assumes r m = 1" |
| a regular generator of the gcd ideal is a regular gcd (when merely a gcd exists); a gcd generates the gcd ideal | `GcdTorsor.Over.At.Generates`, `FromGen.result`, `generates` | — |
| **step 3 through the line**: the regular gcds of the a_j = the regular generators of the image of a_Det (equal types by univalence); these form an R^x-torsor | `DetFFR.Over.At.Canonical.RegGen`, `gens-equiv`, `gens-eq`, `gens-torsor` | "the torsor of regular gcds not identified with the generators of the image of a_Det" |
| a_Det is injective (top(a_Det φ) = det ev(φ), det regular) | `DetLine.Over.Chain.Res.injective`, `Coordinates.injective` | — |
| **a_1 : Det(F) → R** without choices: J : ∧^1 G(m+1) ≅ R is the top coordinate for the basis given by the resolution's iota; a_1 = J ∘ a_Det, injective, same image as a_Det | `DetGcd.Over.At.J`, `J-value`, `a1`, `a1-inj`, `image-to`, `image-from` | "a_1 : Det(F) → R (∧^1 R = R) not written" |
| for a : K → R linear injective: the bases of K (free generators) ≃ the regular generators of the image of a, by φ ↦ a(φ) | `DetGcd.Free.Gen.Basis`, `equiv`, `FromBasis`, `FromGen` | — |
| **the regular gcds of the a_j are the a_1(φ), φ a basis of Det(F)**: Bases(Det F) = RegGcd (univalence); the bases of Det(F) form an R^x-torsor | `DetGcd.Over.At.gcd-of`, `gcd-equiv`, `bases-eq`, `bases-torsor`, `DetGcd.Over.OfRes` | "torsor of generators of the image, not of bases of Det(F)" |
| iso-induction for a family of modules: (G' : Nat → Mod) × Π_i (G i ≅ G' i) is contractible | `NaturalFFR.Over.pthF` | — |
| a resolution is determined by its maps (the rest of ResOf and the bases are propositions) | `NaturalFFR.Over.At.ResEq.result` | — |
| **an isomorphism of resolutions is an identity of resolutions** (φ_P, φ_i commuting with u, T_i, iota) | `NaturalFFR.Over.At.Compat`, `iso-path` | — |
| **naturality of Det(F) and a_1**: an isomorphism of FFRes of a nonzero ideal gives e : Det(F) ≅ Det(F') with a_1' ∘ e = a_1 (by transport; e = id at refl) | `NaturalFFR.Over.At.DetNatural.natural`, `natural-iso` | "naturality of the canonical Det(F) for isomorphisms of FFRes" |
| **structure identity for rings** (TrueGrade.RD), an instance of the generic SIP (`SipGeneric`): ring structure = +, ×, 1 with axioms; (S' : RD) × RIso S S' contractible; a TrueGradeBase.Iso is an RIso with the same map | `RingSIP.Data`, `ax-prop`, `fields`, `mk`, `total-contr`, `Fd`, `of-iso` | — |
| **instance**: the true grade is invariant under ring isomorphisms, by one iso-induction (koszul/TrueGradeIso.tgr-iso re-derived) | `RingSIP.GradeIso.tgr-iso` | "TrueGradeIso by transport needs a ring SIP" |
| **det of an endomorphism without bases**: the scalar Δ by which ∧^n V acts on the top line (unique, exists, an element); for every basis Δ = det of the matrix | `DetEnd.Over.At.IsDet`, `Delta`, `delta-is-det`, `delta-coords`, `Basis.lam-omega` | — |
| **Wiebe's theorem without bases** (ctete Thm 11): α, β linear forms on F ≅ R^n merely, β ≡ α∘V mod J, Gr(β) ≥ n mod J ⇒ mod (J, β): Δ⊥ ⊆ (α) and (α)⊥ ⊆ (Δ), Δ = det V; ideals of the forms, no basis or elementary operation in the statement | `WiebeFree.Over.At.theorem`, `Hyp`, `GradeHyp`, `Perp`, `Ann`, `InB`, `InBA`, `InBD` | "Wiebe's `eop` invariance" (now: the statement is invariant under any change of basis) |
| one basis suffices for Gr(β) ≥ n | `WiebeFree.Over.At.grade-from` | — |
| a linear form in a basis: λ(v) = Σ c_k (e v)_k, (c) = image of λ | `WiebeFree.Over.At.Coords.Form.at`, `in-c`, `from-c` | — |
| two injective linear a : K → R, a' : K' → R with the same image: a unique linear iso e with a' e = a | `DetCompare.Free.Compare.equiv`, `commutes`, `unique` | — |
| **(Det F, a_1) depends only on the ideal**: for two resolutions F, F' of the same nonzero ideal (any lengths), a unique e_(F,F') : Det F ≅ Det F' with a_1' e = a_1; e_(F,F) = id, composition; the iso from an isomorphism of resolutions is e_(F,F') | `DetCompare.Over.Pair.e`, `Pair.unique`, `Laws.comp-id`, `Laws.comp`, `FromIso.natural-eq` | "Det(F) for non-isomorphic resolutions not compared" |
| **the zero ideal is decided by a resolution**: all a_j = 0, or the regular gcds form an R^x-torsor (by the number r_1) | `DetCompare.Over.Decide.result` | "not both 0" as a hypothesis |
| supporting: coordinates Lam M ≅ Lam n for a basis; the top line at a degree k = n; ∧f in coordinates is Λ of the matrix | `TopLine.Over.Inverse`, `TopBasis`, `ExteriorDegreeM.Over.Square` | — |

Units: `pn/PicardUnits` (linked) as `Torsor.Ab`; torsors as `torsor/Torsor.TorBase.TorStr`.
