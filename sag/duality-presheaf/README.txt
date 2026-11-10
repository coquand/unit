Duality, Tier 2: the modal Yoneda lemma (unit/sag-model/DUALITY.md)
===================================================================

Check from unit/:   ./segc sag/duality-presheaf all

No new axioms beyond the named premises.  The premises are the fields of
the records in T2.seg (DUALITY.md §3, rows S2.1-S2.4, S2.6, S2.8); every
other statement here is proved from them.  Shared files (Base, Prelude,
Paths, Equivalences) are read-only symlinks to ../tensor.

Reading (A), as Tier 1: internally to cSet, Unit being its internal
language.  Sub and El of the presheaf CwF are Unit types (no isSet
fields); the CwF laws are Unit Id (internal paths).  The paper's strict
equations are an instantiation obligation (DUALITY.md §4).  Coherence
discipline: laws are used only where the goal is an equivalence or a
proposition, and no proof compares two law-paths (no 2-cells).
isSetTy (types form a set) is the one premise standing for strictness of
types; it is used only through TE.teAny (Lemma72.lpt-ext, Remark 60's
exchange).  Sub and El are not sets.
Restriction: points Sub (yo x) G are Unit types, so every context is
levelwise fibrant; where the paper says "naturally in Gamma" this is
read for levelwise fibrant Gamma (the contexts used, 1.Pr and extensions
by fibrant D-modal types, are).

T2.seg        records PCwF, Site, PiS, DS, ModPi, LocRep (Def 70); module
              Der: wkp, trE, Map, postAt, restr, lift, extEquiv (Sub D (G.A)
              = Sigma s. El D A[s]); Der.Pts: pts, fib, LEqC, LEqT.
Lemma66.seg   P2.1 Lemma 66 (2-out-of-6), proved in Unit: L66.ea, L66.ec.
Lemma67.seg   P2.2 Lemma 67 for context maps: L67.D67[..].lemma67.
Prop69.seg    P2.3 Prop 69: P69[..].prop69.
TE.seg        transport identities (J on one path) and the TE relation.
Lemma72.seg   P2.4 Lemma 72 (= 59): L72[..].lemma72 on ev72; lpt-ext.
Remark60.seg  P2.5 Remark 60: R60[..].At[x, g].Pt[s].remark60 (the square)
              and R60[..].At[x, g].remark60-eq (2-out-of-3 form); the
              exchange G.A.S[p] / G.S.A[p], evCompare (two presentations of
              the domain), all through subExt (extEquiv) and TE.
