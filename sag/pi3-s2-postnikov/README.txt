pi3-s2-postnikov: pi_3(S^2) = Z by a Postnikov universal property.
Informal proof and status: ../../doc/pi3-s2-postnikov.pdf.
Check: ./segc sag/pi3-s2-postnikov all   (from unit/)

CHECKED, unconditional
  SphereAxiom           S2 axiom (segment parameters); Map_*(S2,X) = Omega^2 X, natural
  HomotopyClasses       [X,Y]_* as sets, composition, category laws
  HomotopyGroups        pi3 as a group, functor on maps and on classes; GIso
  LoopIso               isomorphisms of pi_1 from maps of loop spaces
  PostnikovRealization  Fib k (k : K(A,2) -> K(B,4)) is a simply connected
                        3-type with pi3 = B as groups
  ConnectedMaps         connected maps eliminate into truncated families
  Truncations           finite truncations T_m, m >= 1, from replacement
  TruncationProps       pointed universal property; pi3 of the unit bijective
  SphereTruncation      S2 simply connected; trunc3 : Trunc3 for S2
                        (informal proof: ../../doc/finite-truncation.pdf)
  CircleProperty        recursion on N and Z; K(Z,1) has the universal property
                        of the circle: (K -> Y) ~ (y : Y) * (y = y), F |-> (F k0, ap F g);
                        pointed: evPt : Map_*(K(Z,1), Y) ~ Omega Y, F |-> (loop F) g,
                        evPt (F, pF) = pF^-1 . ap F g . pF;
                        PtMap K(Z,1) Y is connected when Omega Y is
  H3Proof               h3 : KZ2Cohomology.H3, [K(Z,2), K(B,3)]_* is a point
                        (informal proof: ../../doc/circle-torsors.pdf)
  CupSquare             a constructed, normalised cup square kappa : K(Z,2) ->pt K(Z,4):
                        Omega Map_*(X,Y) ~pt Map_*(X, Omega Y); c2 : K(Z,2) ->pt Map_*(K(Z,2),K(Z,4))
                        by delooping (Cor. 11) from the circle property; kappa x = (c2 x) x;
                        cup-norm: looping c2 and evaluating at g gives back iota
                        (informal proof: ../../doc/cup-square.pdf)
  H4Classes             [K(Z,2), K(B,4)]_* = deloopings of zero (Unloop f0); conn-rt-n, pi-set
  H4Diagonal            Theorem A: every class is the diagonal of a unique bipointed map
                        K(Z,2) ->pt Map_*(K(Z,2), K(B,4)) (DW1 Lemma 9 over the based path space:
                        the defect of a diagonal, Prop. 11)
  H4Bilinear            Theorem B: g |-> c2 ; K(g,4)_* is a bijection Hom(Z,B) -> Map_*(K2, Map_*(K2, K(B,4)))
                        (cup-norm, naturality of E, H2: Hom(A,B) = Map_*(K(A,2), K(B,2)));
                        Lev: e_m and K(h,m) locked after their by-definition lemmas (eA-def, eB-def,
                        K-def) and loopK; Bridge.eB-eA: e_m of Lev[A,C] target = e_m of Lev[C,B] source
  H4Proof               h4 : KZ2Cohomology.H4 CupSquare.kappa, all abelian B
                        (informal proof, refereed: ../../doc/h4.pdf)
  FibreH3               fib-h3 : [Fib kappa, K(B,3)]_* is a point, all abelian B, for any kappa
                        with (H4): the fibre restriction of F deloops to G; F gives an explicit
                        null-homotopy of kappa ; G (constancy on the 2-connected fibres is a
                        proposition and spreads along K(Z,2)); G = K(g,4), so (H4) gives G = 0;
                        then F factors through K(Z,2) and (H3) kills it
                        (informal proof, refereed: ../../doc/fibre-h3.pdf)
  MapFib                the mapping theorem for targets Fib k: for every triple (A,B,k),
                        q_* : [P, Fib k]_* -> [P, K(A,2)]_* is bijective (lifting lemma for a
                        source Q with (E) F;k merely 0, (U) [Q, Omega K(B,4)] merely 0, used for
                        Q = P and Q = S2); sigma : S2 ->pt K(Z,2) with sigma^* an equivalence on
                        maps into 2-types; s = p_*^-1 [sigma]; rep-fib: s^* : [P, Fib k]_* ->
                        [S2, Fib k]_* bijective; rep-pteq along pointed equivalences
                        (informal proof, refereed: ../../doc/mapping-fib.pdf)
  Presentation          a Postnikov presentation of T = ||S2||_3: V = ||T||_2 ~ K(Z,2) (psi);
                        Rec: a 2-connected 3-type F is K(Omega^3 F, 3); the fibres E z of
                        T -> V carry homogeneous structures mu (Lemma 4 over the simply
                        connected T extends the one at the base point), so z |-> (E z, mu z)
                        is a map V -> K(B,4) = K(B,3)-torsors with fibres E z; kT = psi ; k',
                        Fib kT ~ T, merely pointed.  Final.sT: the mapping theorem at T;
                        Final.pi3-S2 : GIso[pi3 S2 base, ab-grp Zab], UNCONDITIONAL
                        (only the sphere axiom)
                        (informal proof, refereed: ../../doc/postnikov-presentation.pdf)
TOWARDS pi_4(S^3) = Z/2 (doc/cross-term.pdf, refereed; doc/pi3-s2-postnikov-handoff-10.txt)
  Z2                    Z/2 as an Ab (Bool, xor), the parity rho : Hom(Z, Z/2), twoH, zeroH, 2 = 0
  Doubling              pointing irrelevance on PMO_m (any A); K(0,m) = 0; doubling on
                        Omega K(A,m+1) is conj_m K(2,m) (all m); over Z/2 it is constant
  CrossTerm             the cross term of kbar = kappa ; K(rho,4) vanishes: Lemma E2
                        (E (K(2,2) ; c) = E c . E c, pointwise), Theorem 10 (K(2,2) ; c2 ;
                        K(rho,4)_* = 0, so kbar o K(2,2) = * by N), tau (translation in
                        PMO, a pointed equivalence via PtMapLoops ev/unev), the cross term
                        delta = e_2^-1 ; Dhat ; tau ; Cj, its diagonal is null, and by
                        Theorem A delta = 0 (cross), so f = D_p for every p (cross-cell),
                        f = e_2 ; kbar ; e_4^-1.  K(rho,4), e_2, e_4 and K(2,2) in f are the
                        locked Lev ones; Lemma E2 uses the raw KK.e 1 / KMap.K (e1-def)
  DeloopR               Unloop f is contractible (Levels[2,1], cells from cross-cell, no
                        pointing in p); Fhat : K(Z,3) ->pt K(Z/2,5), BR = Fib Fhat:
                        Omega BR ~pt R = Fib kbar, BR isTrunc 6 and isConn 4; a homogeneous
                        structure mu on R, the torsor homog mu, PT contractible (cor8) and
                        Tor_R deloops R.  No S^3 axiom: BR is the candidate delooping, its
                        universal property is step 3 of handoff 9
  Conj                  conjugation by two arbitrary pointed equivalences (different degrees
                        and groups on the two sides): conj, unconj, conj-unconj, unconj-conj
                        (doc/br-universal.pdf, Conventions; conj.opens)
  Necessity             doubling detects the coefficient (doc/br-universal.pdf, Section 5;
                        necessity.opens): EPre.e-pre (E is natural under precomposition in
                        the second variable, ccr-ev), Quad (Proposition Q: K(2,2) ; c2 ;
                        K(2,2)^# = c2 ; K(4,4)_*, kappa (2x) = K(4,4) (kappa x), the classes),
                        Nec (Lemma N: for G^ : K(Z,3) ->pt K(B,5) and [unconj (loop G^)] =
                        Phi h, h 1 + h 1 = 0), Factor (h = rho ; g), Psi (Psi g = Phi (rho ;
                        g), injective), Conv (the numerical converse: Unloop (cj (kappa ;
                        K(h,4))) inhabited gives 2 h = 0).  No sphere axiom
  FibreH3 (generalised) FibAtC[C, k, inj, B]: [Fib k, K(B,3)]_* = 0 for k : K(Z,2) ->pt K(C,4)
                        with g |-> [k ; K(g,4)] (PhiC) injective; FibAt[kappa, h4k, B] is the
                        instance C = Z
  MapBR                 Section 4 and 6 of doc/br-universal.pdf (br.opens): LiftG (the lifting
                        lemma for any k with Omega W, Omega Fib k connected), Triple3 (level-3
                        triples K : K(A,3) ->pt K(B,5)), SourceBR: PStar, fseq, UR (FibAtC at
                        (Z/2, kbar)), UBR, EBR (Lemma N, factor, Psi, loop-eq with the named
                        bridge H4Bilinear.Bridge.eB-eA, unique-loop1), qBR: q_* : [BR, Fib K]_*
                        -> [BR, K(A,3)]_* bijective for every level-3 triple.  No sphere axiom
  Sphere3Axiom          the S^3 AXIOM (segment parameters S3, base, surf, ump3 of Sphere3, as
                        SphereAxiom; not a Theory parameter; s3.opens): ev3, loop3, loop-refl
                        (loop (f, refl) = (ap f, refl)), loop2-comp, loop3-comp, ContractP;
                        Sphere3: evPt, Refl.eq, evPt-subst, pointed-up, evPt-nat (Lemma ev3)
  SourceS3              Section 3 of doc/br-universal.pdf (s3.opens), under the S^3 axiom only
                        (no S^2 axiom): LoopEquiv (Lemma loopeq3, cor11 at any c), g-def;
                        SourceS3: e2 (Lev[Z,Z].eA two at the spelling K three), e2i, c3, sigma3,
                        sigma3-ev (Def. sigma3); Sig3[Z,z0,tZ]: Psi3, the five equivalences
                        e-loop3, e-pre2, e-loop2, e-pre1 (comp2/3/4 with -def lemmas) and the
                        circle property, psi3-equiv, sigma3-nat, sigma3-star, sigma3-cls
                        (Prop. sigma3); LevW5 (Omega^3, Omega^4 K(B,5) connected), s3-paths,
                        ex-S3, un-S3, qS3 (Cor. qS: MapBR.LiftG at Q = S3);
                        Final[S3,base,surf,ump3]: s = qS3^-1 [sigma3] (a class, no
                        representative), s-eq (s ; [p] = [sigma3]), right (PStar + sigma3-cls,
                        comp-assoc, cancel-r), rep-fib (Theorem main: s^* : [BR, Fib K]_* ->
                        [S3, Fib K]_* bijective for every level-3 triple; square qBR, right,
                        qS3, cancel-equiv), rep-pteq (Cor. transfer).  The marked universal
                        property for presented targets, under the S^3 axiom only
  Sphere3Trunc          Lemma s3conn and Proposition trunc4 (trunc4.opens), the text of
                        SphereTruncation one level up: pi4 X = pi3 (Omega X), pi4-map F =
                        pi3-map (loop F); loopC (looping on classes; loopC-comp, loopC-id),
                        pi4C = pi3C o loopC (pi4C-beta-at, pi4C-comp, pi4C-id; locked after
                        pi4C-def); Interfaces4.Trunc4 (Interfaces.Trunc3 one level up);
                        Sphere3Trunc[S3,..]: ev-base-equiv (into 2-types), Simply.s3-conn
                        (S3 isConn 4), Truncate (connT, the fibres of the loopings of eta
                        isConn 5..2, pi4-eta by ConnPi1 on loop^2 (loop eta)), trunc4 at
                        TO three / TO five.  Under the S^3 axiom only
  Presentation4         Theorem pres4 (pres4.opens), the text of Presentation one level up:
                        Rec4 (F isConn 5, isTrunc 6 is K(B,4), B = Omega^3 (Omega F): Rec at
                        Omega F, then deloop-equiv with Cor. 11 at c = 3); Classify[n, S]
                        (tau and Lemma 11 at any stage; used at n = 2: K(B,5) = K(B,4)-
                        torsors); Pres4[Y,y0,cY,tY] for every pointed 2-connected 4-type:
                        V = ||Y||_3, e_V = Rec at V (A = Omega^3 V), e4 = Rec4 at E v0 (B
                        ARBITRARY, not identified), Q, q-set, ext, mu, k1, kp, tot, K = e_V ;
                        kp, fib-K, pres-pt (merely pointed), pres; Final4[S3,..,TR].rep-T:
                        s^* : [BR, T]_* -> [S3, T]_* bijective for a level-4 truncation TR of
                        S3 (rep-pteq, eliminated from pres-pt).  Under the S^3 axiom only
  Pi4Sphere             Theorems up and final (pi4.opens): pi3-pe (pi3 of a pointed
                        equivalence, LoopIso), pi4-BR : pi4 BR = pi3 (Omega BR) ~ pi3 R ~ Z/2
                        (omega-BR, Triple[Z, Z/2, kbar].pi3-iso); Two4 (SphereUniversal.Two one
                        level up, on classes, with pi4C); Assemble4 (P = BR, s = Final.s,
                        sP = Final.rep-fib at (Z, Z/2, Fhat), sT = Final4.rep-T);
                        Pi4S3[S3,base,surf,ump3].pi4-S3 : GIso[pi4 S3 base, ab-grp Z2ab],
                        trunc4 instantiated inside: UNCONDITIONAL beyond the S^3 axiom (and the
                        Theory parameters univalence, images, surjectivity)
CLASSIFICATION of pointed simply connected 3-types (doc/postnikov-classification.pdf;
Hart-Milner, Classifying 2-Groups in HoTT, LICS 2026, Lemma 40, Theorem 41 (Owen Milner's
equivalence, per the Agda README), Note 42, at n = 2 and simply connected; Agda branch lics,
commit 9ec62dd; classification.opens)
  ClassAb               paths in Ab from additive bijections (ab-path: eqind; the rest of the
                        structure is a proposition for a given addition)
  ClassBase             PtProp/StageId: (u = v) ~ (u ~pt v) for pointed types with a property and
                        for EM.Stage[n] (J); stage-gpd: Stage[1] is a 1-type; conn-lift (isConn at
                        l to l+); const-contr ((z : Z) * (d -> z = g d) contractible, D 1-connected,
                        Z a 1-type); conn-back, total-conn; ap-equiv, subst-cancel, pair-path
  ClassEM               Theorem 38 at n = 2, 3: K2 : Ab ~ Stage[0], K3 : Ab ~ Stage[1] (Rec2 = the
                        steps G1, G2 of Presentation.Rec at a 1-connected 2-type; Band2, Band3:
                        Omega^n K(B,n) ~ B additive)
  ClassFib              Theorem 41 at a simply connected base V: (W : Stage[1]) * V ->pt Tor W ~
                        Fam V = (F : V -> U) * F v0 * ((v) -> F v 2-connected 3-type); TorW (tau =
                        Theorem 36(1), Tor ~ TorL), Key (Lemma 9: S F is a proposition, by
                        const-contr over Sigma F), Chain.fib-equiv
  ClassPost             SC3 = (X : U) * (x : X) * isConn 3 X * isTrunc 5 X; Lemma 40: alpha :
                        (V : Stage[0]) * Fam V ~ SC3 (delta X = (||X||_2, fib eta, ..); DA: ehat,
                        its inverse by ConnectedMaps.null, t, coh, sip)
  PostnikovClassification  Triples = (A B : Ab) * K(A,2) ->pt K(B,4); realise (A,B,k) =
                        (Fib k, (pt, k0), conn3, trunc5) (PostnikovRealization.Triple); chain (Theorem
                        38 on the bases, ClassFib, ClassPost); realise-agree (Note 42);
                        realise-equiv : isEquiv Triples ClassPost.SC3 realise and classification =
                        (realise, realise-equiv) : Equiv Triples SC3 in U (l+1), UNCONDITIONAL
                        (only the Theory parameters; no sphere axiom)
  Pi3Classified         Final[S2, base, surf, ump]: rep (MapThm for every simply connected
                        3-type X: MapFib.Final.rep-fib at the triple sec X, transported along
                        realise-equiv.sec-eq X), map-thm, pi3-S2 : GIso[pi3 S2 base, ab-grp Zab]
                        (Pi3Sphere.Conditional.pi3-S2-T); only the S2 axiom
DELOOPING EMBEDDING (doc/delooping-embedding.pdf; David Wärn's idea; embedding.opens)
  DeloopEmbedding       SC4 = pointed 2-connected 4-types (isConn 4, isTrunc 6; ClassBase.PtProp),
                        Omega : SC4 -> SC3; LoopEq: loopPE has the section delta (SourceS3.LoopEquiv
                        at c = 2, Whitehead), loop-delta; Theorem E: (v) * (Omega u = Omega v) is
                        contractible (retract of (v) * Omega u ~pt Omega v, itself a retract of
                        (v) * u ~pt v), so ap Omega is an equivalence (Emb.emb) and the fibres of
                        Omega are propositions (fib-prop); Corollary C: Deloopable t = fib Omega
                        (realise t), a proposition, sc4-equiv : (t : Triples) * Deloopable t ~ SC4;
                        step 1: deloop-R (BR deloops R = Fib kbar), BR-Tor : BR ~pt Tor_R (the two
                        deloopings agree); Mark[S3,..]: statement M (s^* : [BR, Y]_* -> [S3, Y]_*
                        bijective) and marked: M for every Y : SC4, via Presentation4.Pres4.
                        M for every Y : SC4 WITHOUT Pres4: MarkDirect.Direct.marked (below).  The
                        Crux at A = Z is Statement T with G = id (TwoTorsion.TwoTors.unloop); for
                        general A it is not formalised, and not needed
  MarkLoop              (doc/delooping-direct.pdf, Section 1; markloop.opens) LoopCls: looping on
                        classes [X, Y]_* -> [Omega X, Omega Y]_* is a bijection for X isConn 4,
                        Y isTrunc 6 (SourceS3.LoopEquiv at c = 2, classes-equiv);
                        LMark[S3,..]: r = loop s ; [omega-BR] in [Omega S3, R]_*, Proposition L:
                        At[u].to-loop / from-loop, statement M at u iff r^* : [R, Omega Y]_* ->
                        [Omega S3, Omega Y]_* is bijective (loopC-comp, comp-assoc, pre-pteq,
                        2-out-of-3); no presentation
  CrossDeloop           (doc/delooping-direct.pdf, Section 2; crossdeloop.opens)
                        LoopIrr, PtIrr.lambda0 (Lemma (lambda0): pointed maps into a loop space
                        with pointwise equal functions have pointwise equal loop^2: LoopHomotopy,
                        then Eckmann-Hilton, twice); loop2-comp; Inv[X,W]: lam (lambda_g m =
                        loop^2 m g), Delta^f_q (dfun, locked), delta0 (Delta0), lam-zero
                        (lambda2); Delta1.d1 (Delta1, for multiplicative L); lam-pre (lambda1);
                        ELoop.At.e-loop and EDelta.At.e-delta (Lemma (lambda3): (E c)(x) =
                        loop^2 (c ; ev_x) gamma0, and = loop^2 e4 (lambda_{gamma^0} m) when
                        ev_x o c = e2^-1 ; m ; e4 pointwise).  With it: CrossTerm.CrossGen[B, f]
                        (Dp, tau, Cj, delta, cell-of for any B, f; Cross is its instance at Z/2),
                        DeloopR.UnloopGen[B, f, delta = 0] (Theorem 16 for any B: Unloop f
                        contractible), MapFib.FibP[A, B, k] (cp, fseq, (F1) surj2: loop^2 fpr
                        surjective, (F2) const-ext, PStar[C]: p^* bijective on classes into
                        K(C,2), Lemma 7 for any triple; SourceP uses it at (Z, Z, kappa));
                        Necessity.ThetaEq.theta-pt (Theta c = Theta c', the set-level part of
                        theta-eq)
  TwoTorsion            Statement T (doc/delooping-direct.pdf, Section 2.3, Steps 1-6;
                        twotorsion.opens), NO sphere axiom, no presentation: for a deloopable
                        triple (A, B, k) (dl : DeloopEmbedding.Deloopable), Loop[t, dl]: eps :
                        Omega Y ~pt Fib k, pi = eps ; fpr ; e_2^-1 is loop P (Lemma 1: pi-cell,
                        pi-loop, pi-mult), N: pi ; f_k = 0 from fpr ; k = 0; TwoTors[t, dl, G]
                        for G : K(Z,2) ->pt K(A,2): Ghat = e_2 ; G ; e_2^-1 = loop K(a,3)
                        (ghat-loop), f' = f_{G;k} = Ghat ; f_k (f'-eq); Elim[n, w, ew] (the mere
                        N of Step 2 and gamma' of Step 4, (F1), eliminated into the set-level
                        Theta delta = Theta 0): gamma', eg, phi, phi-pi (the only use of
                        deloopability: (lambda0), (Delta1) at L = pi, N, (Delta0), (lambda2)),
                        phi-refl ((F2)), lam-fp, h-cell, e-zero ((lambda3), ETwo.e-zero),
                        theta; then theta, cross (delta_{f'} = 0, theta-inj), CONCLUSION 1
                        unloop : Unloop f_{G;k} (DeloopR.UnloopGen); Two[h, eh] for
                        [G ; k] = Phi_B(h): CONCLUSION 2 two-tors : 2 h(1) = 0 (conj-bridge
                        with Lev.eB-def, Necessity.Conv)
  MarkDirect            statement M for every pointed 2-connected 4-type WITHOUT a presentation
                        (doc/delooping-direct.pdf, Section 3; markdirect.opens): ExR (E) at R =
                        Fib kbar for a deloopable triple (FibP[Z, Z/2, kbar].PStar, h4, Statement
                        T, Factor, Psi, fseq), qR (MapFib.Lifting at R, (U) = MapBR.ur);
                        Direct[S3,..]: RStar, transfer (ptEqInd), rA (r^* bijective into K(A,2):
                        SourceS3.Final.right is M at K(A,3), Proposition L, e_2), ExS, UnS, qS
                        (the source Omega S3: rA, comp-assoc, comp-zero-r; Lemma 1 at (S3,
                        K(B,4)) and s3-paths), rF (r^* bijective into Fib k for every deloopable
                        triple: 2-out-of-3), AtU[u] (u : SC4: the triple realise^-1 (Omega u),
                        deloopable by u; transfer along eps^-1; LMark.At.from-loop), marked :
                        Mark.Marked u for every u : SC4.  The marked class r is MarkLoop.LMark.r
  Pi4Direct             THE NEW ENDPOINT pi4 S3 = Z/2 through the delooping embedding
                        (pi4direct.opens): Assemble (sT = MarkDirect.Direct.marked at the
                        truncation (T, t0, connT, truncT) : SC4, sP = SourceS3.Final.rep-fib,
                        Pi4Sphere.Two4, Pi4Sphere.pi4-BR); Pi4S3[S3,base,surf,ump3].pi4-S3 :
                        GIso[pi4 S3 base, ab-grp Z2ab], UNCONDITIONAL beyond the S^3 axiom.
                        It does NOT depend on Presentation4 (Pres4, Final4) nor on
                        DeloopEmbedding.Mark.marked: checked by deleting Presentation4.seg,
                        Mark.At / Mark.marked and Pi4Sphere.Assemble4 / Pi4S3 in a copy of the
                        development, which still checks (4874 declarations, 0 failed).
                        Pi4Sphere.Pi4S3 (through Pres4) is kept unchanged as the reference
CHECKED, CONDITIONAL on explicit interfaces (not Theory assumptions)
  SphereUniversal       Trunc3 + Rep  =>  pi3 S2 = pi3 P (two-map Yoneda); Two: the same from
                        the two instances sP (X = P), sT (X = T) of Rep.rep
  Pi3Sphere             kappa + Trunc3 + MapThm(Fib kappa)  =>  pi3 S2 = Z;
                        pi3-S2-T: kappa + MapThm, with the constructed Trunc3
STATEMENTS
  KZ2Cohomology         H3 (proved: H3Proof.h3), H4 for kappa (proved: H4Proof.h4)
DONE (28 Oct 2026): SC3 ~ Triples by the fibre realisation, PostnikovClassification.classification.
DONE (28 Oct 2026): pi4 S3 = Z/2, Pi4Sphere.Pi4S3.pi4-S3, from the S^3 axiom alone.
DONE (28 Oct 2026): pi4 S3 = Z/2 using David Wärn's delooping embedding, Pi4Direct.Pi4S3.pi4-S3 (not his
intended route: arbitrary maps between triples are not classified; doc/pi4-s3-embedding.pdf): M for
every pointed 2-connected 4-type (MarkDirect) from Statement T (TwoTorsion: the cup-square
calculations of CrossDeloop, CrossTerm.CrossGen, H4Bilinear underneath), no presentation.
DONE (28 Oct 2026): pi3 S2 = Z, Presentation.Final.pi3-S2; MapThm is only needed at X = P and
X = T, where it is MapFib.Final.rep-fib and Presentation.Final.sT.  Since the classification,
MapThm holds for EVERY pointed simply connected 3-type X (Pi3Classified.Final.rep: rep-fib
transported along realise (sec X) = X), and Pi3Classified.Final.pi3-S2 obtains pi3 S2 = Z from
it through Pi3Sphere.Conditional.pi3-S2-T, without Presentation.Pres.
twotorsion.opens, markdirect.opens, pi4direct.opens, markloop.opens, crossdeloop.opens,
embedding.opens, classification.opens, pi4.opens, trunc4.opens, pres4.opens, s3.opens, conj.opens, necessity.opens, z2.opens, double.opens, cross.opens, deloop.opens, pi3.opens, truncation.opens, circle.opens, cup.opens, h4.opens, fibre.opens, mapfib.opens, present.opens (reproducible; textual audit
against doc/h4.tex not yet done): --opens specifications (seg/WRITING.md,
rule 6), one entry per declaration; a checker diagnostic on locks:
../../doc/etav-lock-diagnostic.txt.
