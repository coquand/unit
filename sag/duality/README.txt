Duality, Tier 1: the algebra in the base (unit/sag-model/DUALITY.md)
=====================================================================

Check from the repository root:
  ./segc sag/duality all

Builds on ../tensor (and through it ../presentations) without modifying
it; the shared files are read-only symlinks.  Foundation as there:
univalence and replacement (Theory parameters).  The generic files use
only fe and the pushout property; replacement enters only through the
quotients behind Presented.seg.

BaseChange.seg   jonas.pdf Lemma 50, generically from a pushout square
                 (tensor/Pushout.seg Square.Pushout): induced maps and
                 their uniqueness; Compare.move between two base changes
                 and its uniqueness; identity-law; Composition.law;
                 Retraction (r, id_B); Diagonal.q with q-up, q-j.
Representability.seg
                 Prop 58, base part: At[A,P,p,B,ch].forward,
                 representation (an equivalence), evaluation (the base
                 half of the evaluation clause of Construction 57).
Presented.seg    chosen presentations give base changes (no truncation).

Note: P here is an R-algebra presented over R with an arbitrary
p : A -> P; the paper's <u>_{T/A} is presented over A.  Tier 1 is generic
in p; the comparison belongs to Tier 3 (S3.6, Construction 55).
