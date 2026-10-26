# sip: the structure identity principle, once

The SIP is proved once, generically, after Escardó (*Introduction to
Univalent Foundations*, the notions of structure and their combinators) and
Rijke (*Introduction to Homotopy Type Theory*, Thm 11.2.2, the fundamental
theorem of identity types).  Modules and algebras are instances.  The only
algebraic fact each instance contributes is that its axioms form a
proposition.  Check from the `unit` root with `./segc sag/sip all`
(20 modules, about 0.1 s; at most 369 openings per declaration).

| file | content |
|---|---|
| `SipGeneric` | `Notion` (S, Iota, rho, unit), with the pieces `binop`, `action K`, `point`, `join`, `axioms`; `Over[N].total-contr` (one `eqind`); `Fundamental[C,I,idI,tc]`: `sip`, `idToIso`, `sip-id`, `idToIso-sip`, `sip-idToIso`, `sip-equiv`, `iso-ind`, `iso-ind-beta`, `Transport.theorem` (ap_G (sip φ) = ua (G φ)) |
| `AbAxioms` | `Ab`: abelian groups as a property of +; zero and negation are axioms, unique given associativity and commutativity (`zero-uniq`, `neg-uniq`, `ax-prop`) |
| `ModuleSIP2` | `Over[Rg]`: the module notion, the record bridge (`fields`, `mk`, `back`), and the names of pn/ModuleSIP and cffru/ModuleSIPFull |
| `AlgSIP2` | the algebra notion and the names of pn/AlgSIP and AlgSIPInd; `sip-same`: its `sip` is AlgSIP's |

## As a replacement for the old proofs

The isomorphism types are definitionally the old ones (`same`, `same'`):
`LinEquiv` is ModuleSIP's, and `AlgIso` and `Hom` are AlgSIP's.  `idToIso`
is the old one by definition (`idToIso-same`), and `sip-same` proves
`sip = AlgSIP.sip`.  So a user switches by changing the module name.

Switched (2026-10-26; each directory imports `SipGeneric`, `AbAxioms`,
`ModuleSIP2`, and chatelet also `AlgSIP2`, through links to `../sip/`):

- chatelet: `Lemma341`, `SkolemNoether`, `SkolemNoetherConj`,
  `SkolemNoetherIso`, `TriangleRI` (iso-ind from AlgSIP2, not AlgSIPInd),
  `DescentLinear`; `Prop331` takes `sip`/`idToIso` from AlgSIP2 and the Sigma
  representation `At` from AlgSIP (`AO`), as `Prop331Str` does;
- cokernel7: `LocalisationEq`; picard: `LineAssociated` (also linked in
  chatelet and pn).

`./segc sag/DIR all` passes for chatelet, cokernel7, picard and pn.

Not switched:

- `exterior/` (frozen) and `pn/AlgSIPInd`, `pn/AlgSIPTransport` (the old
  proofs themselves): pn/AlgSIP stays.
- chatelet `Prop331Str`, which builds on `AlgSIP.At[X]`, the old Sigma
  representation of the data; the new one is `S.Str` with `fields`/`mk`.
- cffru (`FreeModules`, `ModuleSIPFull`, `ExteriorFree`, and ModuleSIPFull's
  users `FiniteFree`, `Lines`, `NaturalFFR`): another session works there.
  ModuleSIP2 has ModuleSIPFull's names with the same types.
- For pn/ModuleSIP, `sip = ModuleSIP.sip` is not proved (the old file only
  has the one direction).  Its users use it only as a path.

| | old | new |
|---|---|---|
| lines (ModuleSIP, ModuleSIPFull, AlgSIP, AlgSIPInd, AlgSIPTransport) | 469 | 494 (4 files, with the comparison lemmas) |
| max openings per declaration | 2005 (`ModuleSIP.Core.base`), 922, 663 | 369 (`AlgSIP2.sip-same`), 235 |

`eqind` is now copied in four files (torsor/Torsor, schemes/SigmaTools,
affine/AlgebraPointsIdentity, SipGeneric); it belongs in `core/Axioms`.
