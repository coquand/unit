# Flatness of A[X,Y][1/J]/(F,G) over any commutative ring

Formalisation of `../HANDOFF-ETALE-FLAT.md`, first objective: two equations
in two variables.  **The final theorem has no hypothesis**: the noetherian
input is supplied by the coded subrings of `sag/noetherian` (Hilbert's basis
theorem over Z, Coquand--Persson), following canonicity-69's
`doc/jacobian-noetherian.tex`.  The earlier route modulo the interface
`Noetheriannote` (N and D) is kept, and is now superseded.  This is **not** a formalisation of the flatness of all
étale or smooth morphisms (see "Remaining steps").

Check from `unit/`:

    cabal build exe:seg --offline
    ./segc sag/etale-flat all          # 121 modules, 0 failed, about 2 s
    # fresh process, no --only filter:
    SEG=$(cabal list-bin exe:seg); cd sag/etale-flat; timeout 55 "$SEG" All.seg
    # All.seg: 6742 declarations, 0 failed, 2.31 s

## The construction

For any commutative set-ring `A` (`setA : isSet A.R`) and bivariate
expressions `F G : Bivariate[l].Over[A].Expr`, with `J` their formal
Jacobian determinant (`RegularPolynomial.Over.j`, i.e.
`PolynomialIdentity.Over.Canon.jacobian x y F G`):

    R = A[X][Y]                PolynomialIdentity[l].Over[A,setA].XY.ring
    S = R[1/J]                 LocalizationFlat[l].Fractions[R,J].S  (= PowerLocalization[R,J].ring)
    B = S/(F,G)                EtaleFlat2[l].Over[A,setA,F,G].B      (= QuotientRing of the ideal
                                                                       RegularIdeal.Generated[S,2,(G,F)])
    A -> B                     EtaleFlat2[l].Over[A,setA,F,G].QF.HB
    the A-module of B          EtaleFlat2[l].Over[A,setA,F,G].UB.M   (a Modules[l].Over[A,setA].Module)

Equalities are equalities in these rings (coefficient quotients, fractions,
quotient rings), not of polynomial functions.  `J` is inverted by
localization; no hypothesis is put on `A[X,Y]`.  `J = 0` and the zero ring are
allowed (`EtaleExamples`: for `F = 0`, `S` is the zero ring).

## Main theorems (public names)

Flatness is the finite-relations criterion: `FlatRelations[l].Over[A,C,h].Flat`
says that every relation `sum_i h(a_i) b_i = 0` (`Relation`) is merely
explained by `Explanation` (columns `c_.j` in `A`, generators `y_j` in `C`,
`b_i = sum_j h(c_ij) y_j`, `sum_i a_i c_ij = 0`), for all `n`.  It is
equivalent to the library's predicate for the underlying module:

    FlatRelations[l].Over[A,C,h].equivalent setA setC :
      (Flat -> DescentFlat[l].Over[A,setA].At[Underlying[setA,setC].M].Flat) *
      (DescentFlat[l].Over[A,setA].At[Underlying[setA,setC].M].Flat -> Flat)

0. **Any base, no hypothesis** (the main result):

        module E = EtaleFlat2[l].Over[A,setA,F,G]
        E.flat        : FlatRelations[l].Over[A,E.B,E.QF.HB].Flat
        E.module-flat : DescentFlat[l].Over[A,setA].At[E.UB.M].Flat
        E.regularity  : F, G regular pair modulo every (a_1..a_m)S  (RegularCoded)

   The only parameters are those of `All.seg` (univalence, images,
   surjectivity of images), as in every `sag/` directory.

The conditional route (superseded):

1. Noetherian base:

        module E = EtaleFlat2[l].Over[A,setA,F,G]
        E.Noetherian[nc,noeth].noetherian-flat        : FlatRelations[l].Over[A,E.B,E.QF.HB].Flat
        E.Noetherian[nc,noeth].noetherian-module-flat : DescentFlat[l].Over[A,setA].At[E.UB.M].Flat

   for `nc : Noetheriannote[l].Calculus` and `noeth : nc.Noeth A setA`.

2. Arbitrary base (the final theorem):

        EtaleFlat2[l].Arbitrary[nn,A,setA,F,G].flat        : FlatRelations[l].Over[A,E.B,E.QF.HB].Flat
        EtaleFlat2[l].Arbitrary[nn,A,setA,F,G].module-flat : DescentFlat[l].Over[A,setA].At[E.UB.M].Flat

   for `nn : Noetheriannote[l].Noetheriannote`; no hypothesis on `A`.

Proved without any noetherian hypothesis:

    TaylorCompatibility[l].Over[A,B,h,F,G,x0,y0,gzero,invertible]
      x-compatible n : J.Eq (suc n) x_n x_(n+1)       (and y-compatible)
      x-compatible-below n : J.Eq n x_n x_(n+1)        (and y-...)
      x-formula n : x_(n+1) = bump (n+1) x_n a_n      (by definition; y-formula)
    TaylorTargets[l].Over[A,B,h,F,G,x0,y0,invertible].lift n
      F(x,y) = f - T and G(x,y) = G(x0,y0) below degree n+1, no G(x0,y0) = 0
    PolynomialFlat[l].TwoVariables[A,setA].flat   : A[X][Y] is flat over A
    LocalizationFlat[l].Over[A,C,hC,flatC,j].flat : C flat => C[1/j] flat (j not regular)
    PairSyzygy[l].Over[C,I,f,g].Solve[...].result : (Syz) modulo an ideal I
    QuotientFlat[l].Over[A,C,hC,flatC,f,g].Theorem[regular].flat
      : C/(f,g) flat when f, g is a regular pair modulo every (a_1..a_m)C
    LocalizedReduction[l].Over[R,j,m,gens].kernel : the ideal (gens)S read back in R
    QuotientMap, BaseChange : the ring maps B0 -> B along A0 -> A

## The former hypotheses: `Noetheriannote.seg` (no longer needed)

Nothing in this file is proved, and nothing else is assumed: the theorems
take the records below as arguments.  No declaration without a body occurs
in the new files (checked by a scan; records' fields only).

`record Calculus` (component N):

    Noeth (A : CRing) (setA : isSet A.R) : U l
    polynomial   A setA (noeth : Noeth A setA) : Noeth A[X] ...            (PolynomialRing.Extension[A,setA])
    quotient     A setA m (c : Fin m -> A.R) (noeth) :
                   Noeth (QuotientRing.Over[A,Generated[A,m,c].ideal,..].ring) ..
    localization A setA (c : A.R) (noeth) : Noeth (PowerLocalization.Over[A,c].ring) ..
    stable       A setA (noeth) (c : A.R) :
                   merely (N : Nat) * StableAnnihilator.Over[A].Stable c N

The closure properties are stated on the library's constructions themselves,
so no transport between isomorphic presentations is needed.  Not assumed:
that every ring is noetherian, or stabilization in non-noetherian rings.

`module Reduction[nc]` (component D): `Statement` is

    (A setA n (a : Fin n -> A.R) (F G : Expr A) (p : Fin n -> A[X][Y]) (k : Nat) (uF uG : A[X][Y])) ->
    Identity A setA n a F G p k uF uG ->            -- J^k sum_i a_i p_i = F uF + G uG  in A[X][Y]  (D1)
    merely Descent[A,setA,n,a,F,G,p,k]

where a `Descent` is a noetherian `A0` (`noeth : nc.Noeth A0 set0`),
`h : A0 -> A`, `a0`, `F0`, `G0`, `p0`, `uF0`, `uG0` over `A0` with
`h(a0_i) = a_i`, `BaseChange.map F0 = F`, `map G0 = G` (equality of
expressions), `BaseChange.phi (p0_i) = p_i`, and `identity0` = (D1) over `A0`
with the same `k` (Jacobian of `F0, G0`).  `h` need not be injective; images
of `uF0, uG0` are not required.  Only data and one identity are descended.

`record Noetheriannote { calculus : Calculus ; reduction : Reduction[calculus].Statement }`.

## Informal proof, as formalised

1. *S is flat* (no hypothesis).  `PolynomialFlat`: if `B` is flat over `A`,
   so is `B[X]`: for a relation with all coefficients zero from degree `L` on
   (a common bound exists merely), write `g_i = c_i + X t_i`; the constant
   terms satisfy the relation in `B`, the `t_i` the relation in `B[X]` with
   bound `L-1`; explanations are closed under images, scaling and sums
   (`FlatRelations.Ops`, `Image`).  Twice from `A`.  `LocalizationFlat`: a
   relation among `u^d p_i` (common `d`) gives `j^e sum a_i p_i = 0` in `C`;
   explain `j^e p_i` in `C` and multiply by `u^(d+e)`.
2. *Regularity* (`RegularPair`, `RegularCoded`).  `RegularPair` reduces both
   regularities to a kernel principle (`First.Zero`, `Second.Zero`): an
   identity `F P = sum a_i Q_i` (resp. `G P = F W + sum a_i Q_i`) in `R`
   forces `P = 0` in `E1` (resp. `E2`).  `RegularCoded` proves it for every
   `A`: the identity holds on every curve in `E[T]`; in the coded subring `E'`
   generated by `x0, y0, 1/J` and the constants (noetherian by Hilbert over
   Z), injective in `E`, the lifts of every order give `u = h^n w_n`,
   `h^(n+1) w_n = 0` with `u = P(x0,y0)`, and `CodedSubring.Vanish` gives
   `u = 0`.  The former noetherian proof of the principle, kept as
   `First.Noetherian` / `Second.Noetherian`:  For `a_1..a_m` in `A`, let
   `E1 = S/(a)S`, `E2 = S/(a,F)S` (noetherian by `Calculus`; `J` invertible).
   `F` regular mod `(a)S`: if `f s` is in `(a)S`, `s = u^d p`, then
   `J^k F p = sum a_i Q_i` in `R` (`LocalizedReduction`).  With `N` from
   `stable` for `f` in `E1` and the curve of `TaylorTargets`, the identity
   holds on the curve where the `a_i` vanish (`RegularPolynomial.alone`), so
   `(f - T) P(T) = 0` below degree `N+1` and `P(0) = J^k p = 0` in `E1`
   (`StableAnnihilator.Kernel`); `J` is a unit, so `s` is in `(a)S`.
   `G` regular mod `(F)+(a)S`: same in `E2` with `TaylorLift` for `(G, F)`
   (Jacobian `-J`, `F(x0,y0) = 0` in `E2`), from `J^k G p = F W + sum a_i Q_i`
   (`RegularPolynomial.with`); then `p = f c + sum a_i c_i` in `S`.
3. *(Syz) modulo I* (`PairSyzygy`): `f u + g v` in `I` gives `w` with
   `u - g w`, `v + f w` in `I`.
4. *Correction of a relation* (`QuotientFlat`): lift `b_i` to `p_i`; then
   `sum a_i p_i = f u + g v`; by (Syz) mod `(a)S`, `u - g w = sum a_i u_i`,
   `v + f w = sum a_i v_i`; `p'_i = p_i - f u_i - g v_i` lifts `b_i` and
   `sum a_i p'_i = 0` in `S`; explain in `S` (step 1), map to `B`.
5. *Any A* (`EtaleFlat2.Arbitrary`): from a relation in `B`, common
   fractions give `Y = sum a_i P_i` with `iota(Y)` in `(F,G)S`, hence
   `J^k Y = F uF + G uG` in `R` (`LocalizedReduction`): (D1).  `D` gives a
   noetherian `A0`; over `A0` the elements `J0^k p0_i` of `B0` satisfy the
   relation, so are explained (step 4 over `A0`).  The ring map `B0 -> B`
   (`BaseChange.phi`, `MonoidLocalizationMap`, `QuotientMap`) sends them to
   `J^k P_i` and the explanation along `h` (`FlatRelations.AlongBase`);
   multiplying by `u^(d+k)` gives `b_i`.  No "flatness descends from A0"
   is used.

Differences from the handoff's suggestions, not weakenings:
- `S_C = C[X,Y][1/J_C]` (C = A/I) is replaced by `S/(a)S`, the same ring up to
  isomorphism; the reduction `rho` is the projection, with surjectivity and
  kernel `(a)S` given by `QuotientRing` and `RegularIdeal.Generated`, and the
  noetherian closure is applied to `S/(a)S` directly.  No `A/I` is built.
- (Syz) is used modulo `(a)S` in `S` (no division, no decidability).
- Regularity of `G` modulo `F` uses `TaylorLift` with `F, G` exchanged in
  `S/(a,F)` rather than `JacobianDivisibility` (same argument, one step).

## Files (in import order)

| File | Content |
| --- | --- |
| `TaylorCompatibility` | compatibility of the existing lifts mod `T^(n+1)` and `T^n` |
| `TaylorTargets` | the lift with constant target `G(x0,y0)` for `G` |
| `FlatRelations` | relations, explanations, operations, `Image`, `AlongBase`, `Retarget`, `Underlying`, `Bridge`, `Converse`, `equivalent`, `Self` |
| `PolynomialFlat` | `B` flat => `B[X]` flat; `TwoVariables` |
| `LocalizationFlat` | `Fractions` (common denominators), localization of a flat algebra |
| `EtaleIdentities` | ring identities, generated (see below) |
| `PairSyzygy` | (Syz) modulo an ideal |
| `QuotientFlat` | `B = S/(f,g)` and the correction theorem |
| `LocalizedReduction` | ideals of `R[1/j]` generated in `R`, read back in `R` |
| `RegularPolynomial` | the curve map `R -> E[T]` and the Taylor kernel argument |
| `BaseChange` | `map` of expressions, `phi : A0[X][Y] -> A[X][Y]`, naturality |
| `Noetheriannote` | the interface N (`Calculus`), D (`Reduction`), `Noetheriannote` |
| `RegularPair` | regularity of `(F, G)` modulo `(a)S` from a kernel principle; its proof under `Calculus` |
| `RegularCoded` | the kernel principle for any `A`, by coded subrings (generic in the target ring) |
| `QuotientMap` | ring maps between quotients by generated ideals |
| `EtaleFlat2` | the theorems: `Over.flat`, `Over.module-flat` (no hypothesis); `Over.Noetherian`, `Arbitrary` (conditional) |
| `EtaleExamples` | `F=X,G=Y`; `F=X+X^2,G=Y`; `F=0,G=Y` (`S` is zero); lift compatibility at order 3 |

`EtaleIdentities.seg` consists of ordinary equality proofs generated from
`identities.json` by the existing untrusted generator; Unit checks each step:

    python3 sag/horrocks/ring_normalise.py sag/etale-flat/identities.json sag/etale-flat/EtaleIdentities.seg

`sag/noetherian` (`NatOrder`, `Bar`, `Span`, `PolyPres`, `Hilbert`,
`Transfer`, `Generated`, `Sequence`, `Integers`) and `jacobian`'s `RegularAt`,
`RawMap`, `CodedSubring` are imported inside the segment after `QuotientRing`:
both `sag/noetherian/Generated` and `cffr/RegularIdeal.Generated` are named
`Generated`, and the order avoids the shadowing.  `RegularCoded` adapts
`jacobian/FiniteCoefficients` (written for `(A[X,Y]/G)[1/J]`) to any target
ring.

All other sources are relative links to existing files (`jacobian`,
`polynomial`, `presentations`, `pn`, `cffr`, `exterior`, `horrocks`, ...),
unchanged; the checker, `src/` and `tests.expected` are unchanged.  The same
`univ`, `images`, `surjections` parameters as `jacobian/All.seg`, with `fe`
derived; no SAG axiom.

## `--opened`

All new declarations check in at most 0.05 s.  The largest openings are in
`EtaleFlat2.Arbitrary...Descended` (`image`, `over`, `sends`: about 50
definitions, mostly `Quotient`/`PolynomialRing` internals reached while
matching the quotient ring `B` and its projection through the composite maps
`B0 -> B`), and in `FlatRelations.Bridge`/`Converse`, which open
`DescentLinear.Free`, `Modules.pi` and `Alg73.Reg` to see that a vector of
`Free n` is a function `Fin n -> A`.  These are definitional facts the text
uses; none takes noticeable time.

## Remaining steps

- None for two equations in two variables.  (`Calculus` and `Reduction` are
  not proved, but no longer used by the main theorem.)
- n equations in n variables, `r` equations with an invertible minor, and
  smooth/étale morphisms in general: not done (handoff §9).

## Note on shared sources

During this work another session modified `sag/jacobian`
(`StableAnnihilator.Kernel` now takes `stable` in `result`).  The links
follow the current files and `RegularPolynomial` uses the new signature; a
further change there may require adapting this directory.
