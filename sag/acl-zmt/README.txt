ACL §4 : un élément s avec s, sx, sy entiers, par Čech (sag/acl-zmt)
=====================================================================

Handoff : doc/acl-zmt-handoff.txt.  Notes : doc/finite-lifting.tex,
doc/finite-cohomology.tex, doc/acl-zmt-formalisation.tex (« Deux
raccourcis », « Liste de formalisation »).  La voie cohomologique
instanciée sur l'exemple d'ACL §4.4 est décrite au §6 ci-dessous.

Contrôle (depuis unit/) :

    ./segc sag/acl-zmt all

Résultat (26 octobre 2026, nuit, serveur relancé) : 130 modules, 0 échec, 5,4 s
(aucun fichier au-delà de 2,1 s).  Les 30 fichiers .seg de ce
développement (plus All.seg) sont listés aux §4 et §6 ; les autres sont des
liens relatifs vers les bibliothèques (exterior, pn, polynomial,
noetherian, jacobian/CodedSubring, stoneseq/Integers sous le nom ZInt),
inchangées.

Fondations : comme les autres All.seg de sag (univalence et remplacement
comme paramètres du segment Theory ; extensionnalité des fonctions
dérivée).  Aucun axiome de SAG (Loc, SQC).  L'extensionnalité sert à
SquareZero, ReesLifting.Free et FixedCochain.lmod ; tout le calcul de
Čech (Laurent3 ... CechH1Finite) est sans extensionnalité (égalité
coefficient par coefficient, EqL).


1. CE QUI EST ACHEVÉ (constructions vérifiées, sans hypothèse cachée)
--------------------------------------------------------------------

(a) Correction finie (handoff §4 ; finite-lifting.tex, lemme 1).
    FiniteCorrection.Over[A,C0,C1,d,a,b].Correct : A anneau commutatif,
    d : C0 -> C1 A-linéaire, I = (a,b), N = 1 + longueur de la liste,
    z_N - z_1 dans I C0, r_i dans I^(N-i), v dans I^N C0,
    d z_N - sum r_i d z_i = d v  donnent  h = z_N - sum r_i z_i - v  avec
    closed : d h = 0  et  congruent : h - z_1 dans I C0.  N = 1 (liste vide)
    couvert.  Fixed : toutes les z_i égales à z*, h = (1 - sum r_i) z* - v
    (value).
    I^n M (IdealPowers.Over.Pow) : arbre m = a m1 + b m2 ; `homogeneous`
    construit l'arbre depuis la forme  sum_j a^(n-j) b^j c_j ; sous-module,
    I^(n+1) M dans I^n M, r m dans I^(i+j) M (Mult.pow-mul), image linéaire
    (MapPow).  PowIn : feuilles dans un sous-ensemble S.

(b) Calcul de Čech sur D[X,Y,Z], D anneau quelconque (handoff §6 ;
    finite-cohomology.tex, proposition 1).
    Laurent3 : éléments de Laurent = fonctions coefficients E3 -> D (Z^3),
      polynômes = listes finies de termes, produit (g f)(m) = sum c f(m-e) ;
      localisations = conditions de support (NNX, NNY, NNZ), degré (Hom).
      Les produits par des polynômes commutent (mulP-comm).
    Cech3 : delta0, delta1, d1d0 (delta1 delta0 = 0), linéarité, supports.
    CechContraction : pi, sigma, tau.
      decomp       : q = pi(q) + delta1 sigma(q), tout degré ;
      supp-sigma   : sigma(q) vérifie les supports ;
      contraction  : delta0 tau(b) = b pour b fermé vérifiant les supports,
                     dans TOUT degré (H^1(O(k)) = 0) ;
      pi-deg       : pi = 0 en degré -1.
      Seuls des entiers sont comparés, jamais des coefficients de D.
    CechMonomials : gens d = les exposants (-alpha,-beta,-gamma),
      alpha+beta+gamma = d+1 (binom(d,2) de ceux-ci, liste explicite) ;
      pi-gens : pi(q) = sum_{t in gens d} q(expo t) X^(expo t) pour q
      homogène de degré -d-1.
    CechH1Finite (lemme principal, surjectivité) : pour J = (g_j),
      g_j homogène de degré d_j à exposants >= 0, b 1-cochaîne de O(-1)
      vérifiant les supports et  delta1 b = sum_j g_j q_j  (q_j homogène de
      degré -d_j-1) :
        Reduce.generation :
          b = sum_j g_j sigma(q_j)
              + sum_j sum_{t in gens d_j} q_j(expo t) sigma(g_j X^(expo t))
              + delta0 c ,   c = tau(...) explicite ;
        gen-cocycle : delta1 sigma(g X^(expo t)) = g X^(expo t)  (cocycle
          modulo J).
      Aucun test d'annulation dans D, aucune syzygie de J.

(c) Cochaîne fixe (handoff §3).  FixedCochain.Over[D,a,b].Chart[mu,F,G,..] :
    pour P = mu + a F + b G (mu = X Z^(d-1) sur XZ), theta = mu^-1,
      E-eq    : E f = f - theta P f,  E = a(-theta F) + b(-theta G) ;
      epow-in : E^n f dans I^n L (arbre explicite), feuilles dans S
                (support de la carte et degré -1) ;
      div     : f - E^n f = P u_n , u_n explicite ;
      fixed n : Z^-1 = E^n Z^-1 + P u_n.
    XZ (avec p), YZ (avec q) : les hypothèses de support et de degré ;
    d0-zs : delta0 (0,0,Z^-1) = (0, Z^-1, Z^-1).  ACL : instance pour les
    polynômes d'ACL §4.4 (hypothèses vérifiées par calcul).  Donc, pour tout
    n, delta0 z* est dans I^n K^1(-1) + (P,Q) K^1(-1), composante par
    composante, avec des témoins explicites.

(d) Noethérianité graduée (handoff §5).
    SquareZero : l'anneau B (+) B^r de carré nul.
    GradedDependence.Over[A,..,PA,nA,onto,a,b].Rees[r,e].Seq[rho,deg].dependence :
      A avec une présentation noethérienne codée PA sur laquelle tout
      élément se relève (mere), rho_n dans A^r avec rho_n,k dans
      I^(n-e_k) (0 si n < e_k) ; alors, sous troncation, il existe une liste
      r_(N-1), .., r_1, r_i dans I^(N-i), avec rho_N = sum_i r_i rho_i.
      Preuve : codes dans S = A[T] (+) A[T]^r (Generated, Transfer,
      CodedSubring), marche dans l'arbre de barre le long de codes donnés
      seulement sous troncation (pas de choix dénombrable), extraction de
      la relation à l'indice où Good s'applique (pas forcément le
      dernier), invariant coef_j dans I^j, coefficient de T^N.
    ReesLifting.Over[...].lift : avec G : A^r -> K1 linéaire et, pour tout
      n, d z* = G rho_n + d v_n (v_n dans I^n K0), il existe sous
      troncation h avec d h = 0 et h - z* dans I K0 (finite-lifting.tex,
      proposition 2, cochaîne fixe).

(e) Équations unitaires (handoff §9).
    IntegralSections.Over[...].At[c].integral : iota : A -> L, m_k dans L
      avec 1 = sum e_k m_k et m_i m_j = sum_k m_k gamma_ijk ; alors
      t = sum_l m_l c_l est racine de chi (det(XI - a), a_ji =
      sum_l c_l gamma_lij), unitaire de degré n à coefficients dans A
      (DeterminantTrick.Integral, Cayley–Hamilton).  Pas de base requise.

(f) Un normaliseur réflexif vérifié.
    PolyExpr (expressions en a,b,x,y à littéraux entiers),
    RingNormal.Over[R,a,b,x,y].same-value : deux expressions de même forme
    normale ont la même valeur dans tout anneau commutatif ; la forme
    normale est calculée par Unit (refl).  Aucune unicité des formes
    normales n'est prouvée ni nécessaire.


2. LE THÉORÈME CONDITIONNEL (jalon 2) — À NE PAS LIRE COMME ACHEVÉ
------------------------------------------------------------------

ACLZMT.Over[A,setA,PA,nA,onto,a,b,L,setL,iota,x,y, <modèle de Čech>,
            zs,zs-res,fixed, <F1>, <F2>].certificate :
    || (s : L) * (s = 1 + a r + b t)
               * (s, s x, s y racines de polynômes unitaires sur A) ||
(MonicRoot : f de degré <= m, coefficient de X^m égal à 1, f(v) = 0 par
l'évaluation A[X] -> L de Universal.)

Paramètres visibles (rien d'autre) :
  * A, a, b, avec noethérianité codée (PA, nA, onto) — pour A = k[a,b],
    k corps discret, par Field + Generated + Transfer (pas instancié ici) ;
  * le modèle de Čech, INTERFACE PROVISOIRE : modules K0 -> K1 -> K2 de
    O_W(-1) (d1 d0 = 0), C0 -> C1 de O_W, multiplications X, Y, Z
    préservant la fermeture, produit des sections fermées, restriction
    res : C0 -> L à la carte Z déshomogénéisée (additive, A-linéaire via
    iota, multiplicative sur les sections fermées, res(1) = 1,
    res(X w) = x res(Z w), res(Y w) = y res(Z w)) ;
  * la cochaîne fixe : res(Z z*) = 1 et d0 z* dans I^n K1 pour tout n ;
  * F1 (finitude de M = sum_n H^1(I^n K) sur R) : G : A^r -> K1 et, pour
    tout cocycle w de I^n K1, rho gradué et v dans I^n K0 avec
    w = G rho + d0 v ;
  * F2 (finitude de C = H^0(W, O_W) sur A) : c_1..c_m fermées engendrant
    toute section fermée, 1 combinaison des c_k.
Preuve vérifiée : F1 sur beta_n = [d0 z*], ReesLifting, F2,
IntegralSections ; s - 1 = res(Z(h - z*)) dans I L.


3. L'EXEMPLE D'ACL §4.4 — CERTIFICAT DIRECT (achevé)
---------------------------------------------------

    p = x - a + b x y + 2 b x^2 ,   q = y - b + a x^2 + a x y + b y^2 .

ACLExample.Over[A,setA,a,b,L,setL,iota,x,y,hp,hq].certificate : pour tout
anneau commutatif A avec a, b, tout morphisme A -> L vers un anneau
commutatif et x, y dans L avec p(x,y) = q(x,y) = 0 (donc B = A[x,y]/(p,q)
pour A = Q[a,b] ou son localisé en (a,b)),
    s = (1 + a x + b y)(1 + 2 b x + b y)^2      (l'élément u d'ACL §4.4)
vérifie s = 1 + a r + b t (r, t polynômes explicites, r-ex, t-ex) et
s, s x, s y sont racines de polynômes unitaires de degré 4 sur A.
Les polynômes sont des polynômes caractéristiques (Cayley–Hamilton), pas
le polynôme affiché dans l'article.  Données : m_0 = 1,
m_1 = a + 2b + abx + 2b^2 y, m_2 = b + 2b^2 x + b^2 y,
m_3 = (1 + b y)(1 + 2 b x + b y) ;
    s = a m_1 + b m_2 + m_3 ,  s x = a^3 + a m_3 ,  s y = 2ab^2 - a^3 + b m_3 ,
table m_i m_j = sum_k m_k g_ijk, chaque identité étant de la forme
H = p U + q V vérifiée par RingNormal (refl sur formes normales).
Les m_k sont les composantes Z déshomogénéisées des sections
c_t = tau(P u_1 + Q u_2) de finite-cohomology.tex §4 (t les trois monômes
tous négatifs de degré -4) ; cette origine n'est pas utilisée par Unit.
Les données viennent d'un script NON FIABLE (acl_example_identities.py,
calculs auxiliaires par spécialisation numérique et interpolation) ; Unit
ne vérifie que les identités.  Ce certificat n'est PAS une instance du
théorème conditionnel : F1 et F2 n'y sont pas construits.

Contrôle (ACLControl) : p = x(1+ax), q = y(1+ax) (P, Q ont le facteur
commun Z + aX) : s = 1 + a x, s^2 = s, s x = s y = 0 modulo (p,q), d'où
le certificat (degré 2).  Aucune régularité du couple (P,Q) n'est
utilisée, ni dans ce contrôle, ni dans ACLZMT.


4. CORRESPONDANCE HANDOFF -> FICHIERS
------------------------------------

  §4  correction finie            IdealPowers, FiniteCorrection
  §6  Laurent, Čech, contractions Laurent3, Cech3, CechContraction,
      générateurs de H^1          CechMonomials, CechH1Finite
  §3  cochaîne fixe               FixedCochain
  §5  E = R (+) M, relation       SquareZero, GradedDependence, ReesLifting
  §9  équations unitaires         IntegralSections, ACLZMT
  exemple §4.4, contrôle          PolyExpr, RingNormal, ACLExampleData,
                                  ACLExample, ACLControl
  (outil non fiable)              acl_example_identities.py
  voie cohomologique (§6)         LaurentList, ReesLiftingCong, ACLZMTCong,
                                  CechModules, CechOps, CechF1, CechSections,
                                  CechRestriction, CechZMT, ACLCech, ACLS1,
                                  ACLFinal


5. CE QUI RESTE OUVERT (jalon 3, état antérieur au §6)
-----------------------------------------------------
(Pour l'exemple d'ACL, le §6 remplace les bases de Gröbner, le pont du
modèle de Laurent, F1 et F2 ; voir §6.5 pour ce qui reste ouvert.)

  * Bases de Gröbner (CPersson §2, théorème 11) et élimination : ni
    Buchberger ni l'idéal de Rees J = (P,Q,U-aT,V-bT) ∩ Q[a,b,U,V,X,Y,Z]
    (handoff §7), ni les noyaux de matrices (§8) ne sont formalisés.
  * Le pont du modèle de Laurent (fonctions coefficients modulo (P,Q),
    témoins explicites) vers des modules quotients véritables donnant les
    champs du modèle de Čech de ACLZMT (K0, K1, K2, C0, C1, X, Y, Z, produit,
    res) ; en particulier la déshomogénéisation sur la carte Z exige un
    support fini (les éléments utilisés sont des listes finies, le
    passage n'est pas écrit).  FixedCochain donne la cochaîne fixe dans le
    modèle de Laurent ; son transport à ACLZMT.fixed passe par ce pont.
  * F1 : identification K_N(-1) = sum_n (I^n K_Bh(-1)) T^n sur les trois
    cartes et isomorphisme sur H^1 (§7) ; CechH1Finite donne alors les
    générateurs à partir d'une liste génératrice homogène de J.
  * F2 : pgcd homogène, suite exacte (5), 0 -> A -> C -> L -> 0 et
    relèvements c_t (§8).
  * Q : aucun module Rational n'est utilisé ; tout est énoncé pour un
    anneau A quelconque (et, pour ACLZMT, avec une présentation
    noethérienne codée de A).  La spécialisation à Q[a,b] et à son localisé
    reste une instanciation.
  * La réduction à une équation de Hensel (ACL proposition 4.8, lemmes 4.9
    et 4.10) n'est pas abordée.



6. L'EXEMPLE D'ACL §4.4 PAR LA CONSTRUCTION COHOMOLOGIQUE (achevé)
------------------------------------------------------------------

Suit doc/acl-zmt-formalisation.tex, section « Deux raccourcis » et
« Liste de formalisation » (points 1 à 6 ; le point 7, bases de Gröbner et
pgcd, n'est pas nécessaire pour l'exemple).

6.1 Énoncé final (ACHEVÉ, aucune hypothèse au-delà de « k corps discret »)

  ACLFinal.Over[k,setk,dec].Example[L,setL,iota,x,y,hp,hq].certificate :
    k anneau commutatif (ensemble) avec dec : tout x est 0 ou inversible ;
    A = k[b][a] (PolynomialRing.Extension deux fois, a = variable externe) ;
    iota : A -> L morphisme d'anneaux, x, y dans L avec
      hp : p(x,y) = x - a + b x y + 2 b x^2 = 0 ,
      hq : q(x,y) = y - b + a x^2 + a x y + b y^2 = 0
    (sous la forme PolyExpr de ACLExampleData) ; alors
    || (s : L) * ((r t : L) * s = 1 + a r + b t)
       * (s, s x, s y racines de polynômes unitaires de A[X]) ||
  (MonicRoot v : un degré m, f avec Bounded (m+1) f, coef f m = 1 et
  f(v) = 0 par l'évaluation de Universal.)
  Ce n'est PAS le certificat direct d'ACLExample : s est obtenu par la
  construction cohomologique (correction finie, relèvement de Rees,
  noethérianité codée), et les équations unitaires par la marche
  noethérienne non graduée, sans Cayley–Hamilton.  Aucune donnée calculée
  hors de Unit n'intervient.  La spécialisation à Q (corps discret) reste
  une instanciation.

6.2 Théorèmes intermédiaires, du général au particulier

  ACLZMTCong.Over[...].certificate (CONDITIONNEL, paramètres visibles) :
    variante d'ACLZMT où
      * les égalités dans K1 et C0 deviennent des congruences modulo des
        sous-modules N1, N0 (ReesLiftingCong.Sub) ; res tue N0 ;
      * gen1 est réduit à sa seule instance, les classes
        beta_n : d0 z* - (G rho_n + d0 v_n) dans N1 ;
      * gen2/one-comb sont remplacés par le raccourci (F2) : sections fermées
        (Closed c : témoins), coordonnées kappa(c) dans A^s, Phi : A^s -> C0
        linéaire avec c - Phi(kappa c) dans N0 ; stabilité par produit, 1 fermé.
    Preuve des équations unitaires : GradedDependence avec l'idéal (1,0)
    (tout élément est dans I^n) sur la suite kappa(c^i) ; donne
    c^M - sum x c^(len xs) dans N0, donc res(c)^M = sum iota(x) res(c)^(len xs),
    racine de X^M - sum x X^(len xs) (MonicRel, degré et coefficient dominant
    par CharPoly.Lead).
  ReesLiftingCong.Over[...].lift : ReesLifting avec beta_n modulo N ; la
    correction finie h = (z* - sum r_i z*) - v vérifie d h dans N.
  CechZMT.Over[...].certificate (CONDITIONNEL) : pour deux équations données
    par leurs cartes (FixedCochain : P = muP + a FP + b GP, Q = muQ + a FQ + b GQ),
    instancie ACLZMTCong par le modèle de Čech ; paramètres : la
    présentation noethérienne codée de A, la donnée (S1) pour P, Q, les
    identités entières entre degrés (refl pour des degrés donnés), et
    res P = res Q = 0.
  ACLCech.Over[...].certificate (CONDITIONNEL sur s1 et sur PA, nA, onto) :
    CechZMT sur les cartes de FixedCochain.ACL ; toutes les hypothèses de
    cartes et de degrés par calcul (refl) ; res P = p(x,y), res Q = q(x,y) par
    RingNormal.same-value (formes normales égales par refl).
  ACLS1.Over[k,setk].s1 (ACHEVÉ) : la donnée (S1) pour l'exemple, sur
    A = k[b][a], k anneau commutatif QUELCONQUE.
  ACLFinal.Over[k,setk,dec] (ACHEVÉ) : PA, nA, onto pour k[b][a] (Field,
    Transfer le long de k -> A, Generated avec a et b, CodedSubring ;
    tout élément a merely un code par la règle de Horner sur les deux
    quotients de listes), puis l'énoncé du §6.1.

6.3 Fichiers (liste de formalisation de acl-zmt-formalisation.tex)

  point 1 (listes)       LaurentList : sens coef, produit mulL avec
                         coef (mulL g h) = mulP g (coef h), lemme de
                         regroupement (Regroup.vanish/respects, récurrence sur
                         une borne de la longueur), support fini Fin,
                         filtrage, Descend (choix unique), produit prod.
  point 2 (congruences)  ReesLiftingCong (Sub, correction finie et relèvement
                         modulo N), ACLZMTCong (théorème abstrait, MonicRel).
  point 3 (modèle)       CechModules (SubMod, lmod/tmod par extensionnalité,
                         sous-modules SL/S1/S0 : degré, supports, support fini),
                         CechOps (sigma, tau, pi, produits par un polynôme,
                         d0, évaluation ; congruences NW), CechRestriction
                         (res sur la carte Z : regroupement, multiplicativité
                         sur les listes à exposants X, Y >= 0).
  point 4 (cochaîne)     CechF1 : w_n = (0, E^n Z^-1, E'^n Z^-1) dans I^n
                         (RaiseOp) et d0 z* - w_n dans N1 (FixedCochain.div).
  point 5 (F1)           CechF1, sans l'anneau D = A[U,V] (voir 6.4) :
                         g = muQ P - muP Q = a g1 + b g2, télescopage
                         E'^n - E^n = (E' - E) S_n, delta1 w_n = g q_n,
                         CechH1Finite.Reduce sur A, q_n dans I^(n-1),
                         c_n = tau(...) dans I^n K^0(-1), beta_n.
  point 6 (F2)           CechSections : produit des sections, fermeture des
                         produits, 1 ; F2 sous (S1) : kappa(c) = (a0, w(expo t)),
                         c_t = tau(P sigma(-Q t) + Q sigma(P t)) linéaire,
                         pi(-Qt) = pi(Pt) = 0 (pi delta1 = 0 sur les cochaînes
                         à supports), contraction, section constante de degré 0.
  (S1) de l'exemple      ACLS1.
  assemblage             CechZMT, ACLCech, ACLFinal.

6.4 Failles des deux raccourcis, signalées avant formalisation

  (F1) L'anneau D = A[U,V] est superflu : g* = muQ P - muP Q (mu = muP muQ)
       s'écrit a g1 + b g2 avec g1, g2 polynomiaux, donc la comptabilité
       « degré de Rees » est celle des arbres I-adiques sur A (q_n dans
       I^(n-1), g sigma(q_n) dans I^n, m_t dans I, c_n dans I^n), et
       CechH1Finite s'applique sur A.  (Le g* choisi a degré d+e = 4 et non le
       minimum 3 ; il y a donc 6 générateurs m_t au lieu de 3, sans effet.)
  (F2) « GradedDependence non gradué (e_k = 0) » est faux tel quel :
       l'hypothèse rho_(n,k) dans I^n n'est pas satisfaite ; la bonne
       instance prend l'idéal (1,0), où tout élément est dans I^n.
       kappa dépend des témoins de fermeture, pas seulement de c : la suite
       kappa(c^i) doit être formée avec les témoins des produits, et (S1)
       doit fournir w comme une fonction (w est unique car P est non diviseur
       de zéro ; il est extrait de la troncation).
  Les deux : l'homogénéité, les conditions de support et le support fini
       doivent être transportés partout (sous-modules SL/S1/S0) ; la
       restriction et le produit des sections passent par les listes et le
       regroupement (choix unique).
  (S1) de l'exemple : aucune intégrité n'est nécessaire.  P = -Z^2 a + P0 a un
       coefficient dominant inversible en a, et R = Z^2 Q + (X^2+XY) P ne
       contient pas a ; d'où beta = P w (division, puis (C) et (D)) et
       alpha = -Q w.  (D) : R0' est non diviseur de zéro sur k[b][X^±,Y^±,Z^±]
       par récurrence montante sur le degré en b, puis le coefficient
       dominant Z de X^3 Z + X^2 Y Z + Y Z^3 (descente sur l'exposant de X,
       support fini).  Valable pour tout anneau commutatif k.

6.5 Ce qui reste ouvert

  * (S0)/(S1) pour P, Q quelconques : FAIT, voir §7, y compris le
    contrôle p = x(1+ax), q = y(1+ax) (D0 = Z + aX), ACLControlGeneral.
  * Les identités entières de CechZMT entre degrés sont des paramètres
    (vraies par refl pour des degrés donnés) ; elles pourraient être
    prouvées en général.
  * La réduction à une équation de Hensel (ACL prop. 4.8, lemmes 4.9-4.10)
    n'est pas abordée.


7. P, Q QUELCONQUES : LE PGCD ET LA VOIE COHOMOLOGIQUE (achevé)
---------------------------------------------------------------

La bibliothèque de pgcd sag/gcd (README.txt de ce répertoire ; note
doc/gcd-polynomial.tex) est liée ici par des liens relatifs (GcdDomain ...
HomLambda, et AdditiveSpan, CoefficientProducts, DedekindMertens,
ZeroProduct de sag/mertens).  Elle fournit, pour P, Q homogènes à
exposants >= 0 sur un anneau à pgcd A : D0 = pgcd(P,Q) homogène, P', Q',
P = D0 P', Q = D0 Q' dans Lambda, (S0) pour D0 et (S1) pour P', Q'
(HomLambda.Data).

  CechSections.Sec.F2D (et CT4) : la donnée (F2) pour un diviseur commun
    D0, comme dans la preuve de la proposition F2 : 0 = delta1 delta0 c =
    D0 (P' delta1 u + Q' delta1 v), (S0) annule D0, (S1) donne la syzygie
    (-Q' w, P' w) ; c_t = tau(P sigma(-Q' t) + Q sigma(P' t)) est fermé car
    P Q' = Q P' (cross, depuis fP, fQ : P f = D0 (P' f), Q f = D0 (Q' f)).
    F2 (D0 = 1) est inchangé.
  CechZMTD0 : CechZMT avec F2D ; paramètres D0, P', Q', fP, fQ, s0, s1 et
    les identités de degrés (CONDITIONNEL).
  ACLGeneral.Over[A,G,PA,nA,onto,a,b,<cartes>,...] (CONDITIONNEL sur la
    seule présentation noethérienne codée de A) : CechZMTD0 avec la donnée
    de HomLambda.Data ; toutes les identités de degrés sont prouvées :
    celles des cartes à partir de deg muP = d0+1, deg muQ = e0+1 (hPd, hQe),
    kW = -(e' + d0 + 1), hW1, hW2 (d', e' calculés par le pgcd).
  ACLGeneralK.Over[k,setk,dec,one-nonzero].Charts[<cartes>,...].certificate
    (ACHEVÉ) : pour k corps discret, A = k[b][a] et DEUX ÉQUATIONS
    QUELCONQUES P = muP + a FP + b GP, Q = muQ + a FQ + b GQ homogènes, à
    exposants >= 0, avec un coefficient non nul chacune (conditions de
    forme, refl pour des cartes données) : si res P = res Q = 0 en (x,y),
    il existe merely s = 1 + a r + b t avec s, s x, s y entiers sur A.
  ACLControlGeneral (ACHEVÉ) : le contrôle p = x(1+ax), q = y(1+ax),
    P = XZ + a X^2, Q = YZ + a XY, dont le facteur commun Z + aX n'est pas
    inversible, par ACLGeneralK.
  ACLFinalGeneral.Over[k,setk,dec,one-nonzero].Example[...].certificate
    (ACHEVÉ) : l'exemple d'ACL §4.4 par cette voie générale, sans ACLS1 ;
    même énoncé que ACLFinal (§6.1), avec l'hypothèse 1 /= 0 sur k.
  ACLCech.ResPQ : res P = p(x,y), res Q = q(x,y) (extrait d'ACLCech.Over,
    qui l'utilise ; aucun changement d'énoncé).
  Renommages : le module imbriqué Span de sag/mertens (CoefficientProducts,
    IdealSpan, ...) s'appelle CSpan, et GcdDomain.Field s'appelle FieldGcd
    (collisions avec les fichiers Span et Field d'acl-zmt).
