Theorem local of zmt2-revised.tex with ZMT proved (sag/etale-local-zmt)
=======================================================================

This tree is sag/zmt-general (the proof of ZMT, FinalZMTGeneral) and
sag/etale-local (Theorem local with ZMT as a hypothesis) together: every
file is a relative link to one of them (the files they share are the same
files), except All.seg and TheoremLocalZMT.seg.

Check (from unit/):   ./segc sag/etale-local-zmt all
Result (30 October 2026): 394 modules, 21057 declarations, 0 failed, 14.3 s.

Foundations: the Theory segment of sag (univ, images, surjections;
function extensionality and propositional univalence derived).  No new
axioms.

TheoremLocalZMT.seg  Over[A,setA,m,m-prop,..,dec,rad,E,setE,iota,q,..,q-dec,
    etale,fo].FieldCase[field].theorem : || Local.Statement.Conclusion ||
  Hypotheses: A local residually discrete (m a proposition-valued
  predicate); E etale (formally etale + a presentation, whose generators
  are given to ZMT); q a decidable prime of E containing m E; fo: merely
  E/mE finite over A/m; field: for every output c of ZMT, merely the
  field-case data (TheoremLocal.FieldData) for the B and s of c.
  Proof: Z = FinalZMTGeneral.Theorem gives merely s, s - 1 in m E, and
  B = A[s, s x_i] finite.  At[c]: bs (generators of B and 0), coord
  (merely, from ModuleFinite.spans), sB, s-one (an IEWit as a list of
  generators of m E: wit-to), zmt (merely s^N z in B, by
  CertificateLocalisation.Iso.cleared on an expression of z); TL =
  TheoremLocal.Over[..these..]; theorem eliminates || Z.Conclusion || and
  || FieldData ||.

Remaining hypothesis: the field case (fo and field).
