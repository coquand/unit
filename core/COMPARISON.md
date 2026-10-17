# seg/core against seg/model: final comparison (2026-10-17)

seg/core formalises every result of seg/notes/model.tex (except the Yoneda
remark of §6.2, marked as not needed); seg/model is the frozen quarry.
Same checker binary (the one installed on 2026-10-17), same machine.

## Files, modules, full check

|                          | seg/core            | seg/model                      |
|--------------------------|---------------------|--------------------------------|
| .seg files               | 178                 | 327 (326 loaded by All.seg)    |
| lines                    | 31,120              | 60,323                         |
| modules checked by `all` | 178, 0 failed       | 326                            |
| `./segc DIR all`, cold   | 38.0 s              | 93 s (seg-62's measurement)    |
| slowest file             | 3.64 s (CDSmallFull2) | not measured here            |
| files over 5 s           | none                |                                |

## Lines per layer: core against the model files it replaces

Model files are assigned to a layer by DESIGN.md's quarry lists, plus:
Sigma/Pi (GSig, GPi, GPiFib, FibPiE) and GConn, GFill*, GFibE, GFibExt,
GLocal*, GMapLine, GProbEq, GTrans, GCofEsi under L3; the remaining GExt*
under L5; all GUa*, GYonEq* under L6; all Delta files (D*, Delta*,
Classical) and PosS, PEl*, PUaOp, PCompU, PosetConn, Constr, CSieve, Cat,
IvBase, CylCat under L8.  The boundaries are approximate; the totals are not.

| layer (model.tex)                 | core files | core lines | model files | model lines |
|-----------------------------------|-----------:|-----------:|------------:|------------:|
| L0 metatheory (§1), copied        | 19 | 5,322 | 17 | 5,290 |
| L1 base (§2)                      |  2 |   478 |  4 |   810 |
| L2 relative contractibility (§3)  |  6 |   898 | 15 | 3,031 |
| L3 fibrations, formers (§4)       | 21 | 4,654 | 31 | 6,768 |
| L4 small types, universe (§5)     |  3 |   635 |  7 | 1,376 |
| L5 gluing, Theorem 7 (§6)         | 33 | 6,318 | 28 | 6,286 |
| L6 univalence (§7.1)              | 14 | 2,048 | 24 | 3,365 |
| L7 Comp(1, U) (§7.2)              |  8 | 1,732 | 21 | 2,383 |
| L8 instances (§8): posets + generic Cl = Fib / Delta + generic operations | 22 + 50 | 2,530 + 6,505 | 65 | 9,741 |
| **total**                         | **178** | **31,120** | **212** | **39,050** |

Without L0 (copied unchanged): core 25,798 lines against 33,760 (-24%).

Two layers grew, for content the quarry did not have:
- L3 now contains the naturality of the type formers, stated as moves along
  cartesian maps (CFillMove, CSigNat, CPiCart, CPiNat, CPathCart, CPathNat:
  1,052 lines) and the Path wrapper (CPathFib, 43 lines).  Without them L3
  is 3,559 lines against 6,768.
- L5 contains the universal glue data and Ext over glue data as maps l : D ->
  GD with Theorem 7's naturality (CExtL, CExt7Nat: 254 lines).

The other 115 model files (21,273 lines) are not replaced by any core layer.
They are the earlier direct poset development and its variants (Box*, Esi*,
Ext* without G, Transp*, BC*, Fill*, Fib*, Univ*, ElFam*, PosetModel, ...).
The core final statements do not need them: they are obtained through the
generic layers and the two instances.

## What disappeared

- Lists of faces: every partial element is one sieve; a "list" is notation
  for a union (bigU), so no Partial/PSide/pcs plumbing and no ESI/KESI.
- One notion (RC) and one Move lemma with its laws replace GTransfer*,
  GTransferEq*, TrF/TrEq, GSmallFib's transfer, DeltaClassifier.Sub, GFillX.
- Naturality statements are moves along cartesian maps (types with the
  same or transported fibres), so substitution never needs an equality of
  types; the substitution form follows by tr-move (CTrFib, CTrEq).

## Slowest files (core, cold full run)

| file | time |
|------|-----:|
| CDSmallFull2 | 3.64 s |
| CDOpFull     | 3.55 s |
| CDSmallFull  | 3.33 s |
| CDSmallCl    | 1.78 s |
| CUaFull1     | 1.29 s |
| CPiNat       | 1.15 s |
| CDElHorn     | 1.13 s |
| CDOpYon      | 0.83 s |
| CPi          | 0.79 s |
| CPosEl3      | 0.71 s |

The three Delta files near 3.5 s are long calc chains at concrete indices.
CDSmallFull2 keeps explicit transH endpoints; they save about 1.1 s.

## Where lem enters

Only in the Delta instance: the segment CClassical.Cl takes lem as its
parameter, and lem is applied at exactly one place, CDeltaHornBox.decDeg
(deciding degeneracy).  The poset instance and all generic layers are
constructive, and so is Theorem 7 at any base.
