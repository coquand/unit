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
Presented.seg    chosen presentations over R give base changes.
Relative.seg     presentations with coefficients in an algebra: change of
                 coefficients u.phi along a ring map, eval/zeros/solutions
                 of u.phi in Y = those of u in Y|phi; A-algebras as
                 R-algebras under A (Under.total, structure, under,
                 Lifted = maps under A, equivalence `lifted`).
RelativeChange.seg
                 Lemma 50 as in the paper: for u over A, X presenting u
                 and Y presenting u.h, (total Y, h+, p_{uh}) is a pushout
                 of p_u along h.  Chosen.ch: a base change for every h,
                 by PresentationExistence over B (no truncation).
Points.seg       Construction 57, base part: Points: retractions of p_w =
                 Solutions(w, B), values on generators, evaluation of
                 expressions (naturality).  Spectrum: Hom(<u>, B) =
                 (h : Hom(A,B)) * Solutions(u.h, B), with `generators`:
                 the solution attached to r is r on the generators.

So Tier 1 now works at P = <u>_{T/A}, presented over A, as in the paper
(the earlier caution under S3.6 about presentations over R is resolved
for the base; S3.6 keeps only smallness and Mod_{T,kappa}).
Known residual: Points.Spectrum.generators opens ~50 definitions
(matching BaseChange.On accessors on ch h with RelativeChange.At names).
