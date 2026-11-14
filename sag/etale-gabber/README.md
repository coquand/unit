# Gabber's theorem for the étale topology

This is a self-contained snapshot of the checked development from
`sag/twisted` in the local CANONICITY development. All 425 `.seg` files,
including the library dependencies, are included as ordinary files so that
the proof can be checked without other experimental changes.

The [étale note](../../doc/etale-gabber.pdf) explains the reduction by Hilbert
90 from étale stack gerbes to root stack gerbes. The
[root-topology note](../../doc/gabber-h2.pdf) gives the gerbe and torsion
`H²` statements; the [gluing note](../../doc/gabber-recollement.pdf) explains
the explicit clutching correction that replaces general effectiveness and
Bass cancellation. Their references to `sag/twisted` correspond to the
same module names in this snapshot.

The final theorem is
`EtaleStacks.Etale[R,setR,axioms].Torsion[A,fp,G,stk,n0,torsion].theorem`:
for a finitely presented algebra `A` and a family `G` of étale stack gerbes
over its spectrum, a torsion equality for its class yields, merely, a
family of Azumaya algebras representing that class. As explained in the
étale note, the classes are compared in `H²` of root stack gerbes; the
injectivity of the map from étale `H²` to that group is not proved here.

The proof follows the notes in these files:

- [EtaleTrees.seg](EtaleTrees.seg),
  [EtaleTreeDescent.seg](EtaleTreeDescent.seg), and
  [EtaleTreeClosure.seg](EtaleTreeClosure.seg): constructed étale
  sheafification.
- [EtaleGabber.seg](EtaleGabber.seg): Hilbert 90 and the gerbe theorem.
- [EtaleStacks.seg](EtaleStacks.seg): object descent and the étale torsion
  theorem.
- [GabberTorsion.seg](GabberTorsion.seg) and
  [GabberH2.seg](GabberH2.seg): the root-topology theorems.
- [WeakCancel.seg](WeakCancel.seg) and
  [TwistedCorrect.seg](TwistedCorrect.seg): elementary weak cancellation
  and the gluing correction.

From the repository root, check the entire snapshot with:

```sh
cabal run seg -- sag/etale-gabber/All.seg
```

Checked on 14 November 2026 with the published checker at commit
`e26ed2c35b5a6912a4c8194707ed0343b3740cee`: 425 modules, 19,414 declarations,
0 failed, 13.33 seconds CPU time (13.72 seconds elapsed). Expected
`#fails ok` messages are negative tests, including the rejection of an
étale sheaf as a root sheaf without a proof. The top-level Theory
parameters are univalence and replacement; the final theorem takes the
SAG axioms as explicit parameters. No additional axiom is introduced.
