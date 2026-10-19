SAG Lemma 2.2.4 from Loc and uniform SQC
======================================

Check from the repository root: ./segc sag/sag-uniform all

SAGUniform[l].Main[R,setR,loc,sqc].lemma-2-2-4 is the existing factorization
theorem, with the revised NN-valued weak Nullstellensatz hypothesis supplied
by UniformNullstellensatz[l].Over[R,setR,sqc].wn-nn.

The only hypotheses beyond univalence and replacement are the commutative
set-ring R, Loc, and uniform SQC. There is no additional wn/root-existence
axiom and no choice of a coefficient-list representative of an inverse.

Roots.seg, Group.seg and Mul.seg are fixed snapshots of the other worker's
revised sag/ files, with one provenance comment prepended. Their source
hashes are recorded in snapshot-sha256.json. Other dependencies are links
to presentations/, whose Ring/Poly versions are the original fixed snapshots.
No file in sag/ is modified by this integration.

This isolates the integration check while the other worker continues work.
It does not change or replace sag/'s own entry point.
