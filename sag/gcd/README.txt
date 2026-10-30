A anneau à pgcd => A[X] anneau à pgcd ; k[b][a][X][Y][Z] (sag/gcd)
=================================================================

Preuve informelle (écrite avant la formalisation, points délicats à la
fin) : doc/gcd-polynomial.tex (et .pdf).  Les numéros ci-dessous sont ceux
de la note.

Contrôle (depuis unit/) :

    ./segc sag/gcd all

Révision du 30 octobre 2026 (preuve directe de MRR IV.4.3) :
Gauss.seg conserve gauss-list, GaussAt.gauss et DivPrim.result ; seul le
mécanisme de preuve change. Gauss.Direct prouve le lemme des contenus par
récurrence sur la somme des longueurs (terme constant retiré), puis la
multiplicativité à un inversible près. PolyGcd.integralP utilise le même
lemme avec d = 0. All.seg n'importe plus AdditiveSpan, CoefficientProducts,
DedekindMertens ni ZeroProduct. Aucun module aval n'a besoin de changer.
Contrôle frais : 3975 déclarations, 0 échec, 1,71 s ; contrôle serveur :
89 modules, 0 échec, 1,45 s. Audit --opened : chaque nouvelle déclaration
< 0,01 s ; au plus 8 définitions ouvertes dans Gauss.Direct et 5 dans les
deux nouvelles preuves de PolyGcd. Spécifications : gcd-direct.opens.
Audit --opens : 120 déclarations, « nothing else opened » pour chacune.
Contrôles frais des dépendants : sag/artin-rees, 10622 déclarations,
0 échec (4,74 s) ; sag/acl-zmt, 7274 déclarations, 0 échec (5,90 s).
Les mesures du 26 octobre ci-dessous sont historiques.

Résultat (26 octobre 2026) : 90 modules, 0 échec, 1,5 s (aucun fichier
au-delà de 0,15 s).  Les 20 fichiers .seg de ce développement (plus
All.seg) sont listés au §3 ; les autres sont des liens relatifs vers les
bibliothèques inchangées (pn : anneaux, polynômes, A[X] quotient ;
exterior : CharPoly pour les coefficients et la chaîne qu'il importe ;
jacobian/FiniteJets ; noetherian/NatOrder,
Bar ; stone/Logic ; stoneseq/NatArith, Integers (ZInt) ; acl-zmt :
Laurent3, LaurentList, Cech3, CechContraction, CechMonomials, IdealPowers,
CechModules, FixedCochain).

Fondations : comme les autres All.seg de sag (univalence et remplacement
comme paramètres du segment Theory ; extensionnalité des fonctions
dérivée, quotients A[X] de PolynomialRing).  Aucun autre axiome, aucun
choix, aucun tiers exclu.


1. DÉFINITIONS (GcdDomain.seg)
------------------------------

  Div a b         = (q : R) * (b = a q)        donnée ; jamais décidée
  GcdOf a b       = (d : R) * d | a * d | b * ((c : R) -> c | a -> c | b -> c | d)
  GcdDomain[A]    record : set, dec (x = 0 ou x /= 0), integral
                  (x, y /= 0 => x y /= 0), gcd : (a b : R) -> GcdOf a b,
                  nontrivial (1 /= 0).
  Prim x          tout diviseur commun des coefficients divise 1
                  (Content.Prim, PolyBase.Prim).

Le pgcd est une donnée (unique seulement à un inversible près).  La
divisibilité n'est pas supposée décidable ; seul le test x = 0 sert.


2. CE QUI EST ACHEVÉ (sans hypothèse cachée)
--------------------------------------------

(a) Théorème 11.  PolyGcd.Over[A,G].domain : GcdDomain[A[X]] pour tout
    anneau à pgcd G : GcdDomain[A], A[X] = PolynomialRing.Extension[A,G.set]
    (l'anneau quotient de sag/pn, le même que dans acl-zmt).
    Le pgcd est calculé (gcdP) : f = 0 -> g ; g = 0 -> f ; sinon
    gamma E avec gamma = pgcd(c(f), c(g)) et E la partie primitive du D de
    l'élimination.

(b) Corollaire 12.  Iterate.Over[k,setk,dec,one-nonzero] : pour k corps
    discret (dec comme dans noetherian/Field.seg : x = 0 ou x inversible ;
    plus 1 /= 0), gcdA : GcdDomain[A] avec A = k[b][a] (same-A : c'est par
    refl l'anneau A d'acl-zmt/ACLS1.Over[k,setk]) et
    gcdS : GcdDomain[S], S = A[X][Y][Z], avec a, b, X, Y, Z, fromA.

(c) Proposition 14 (algébrique).  Syzygy.Over[S,G,P,Q,nP] : dans tout
    anneau à pgcd, pour P /= 0, D0 = pgcd(P,Q), P = D0 P', Q = D0 Q' :
      nD0, nP'   D0 /= 0, P' /= 0 ;
      coprime    pgcd(P',Q') | 1 ;
      s0         D0 f = 0 => f = 0                      (S0)
      s1         P' al + Q' be = 0 => w, al = -Q' w, be = P' w   (S1)
      sol-prop   w est unique.
    Lemme 13 (Euclide) : GcdDomain.Gcd.euclid.

Étapes (toutes achevées) :
  Lemme 3 (M)     GcdDomain.Gcd.lemma-M : d | ua, d | ub => d | u pgcd(a,b).
  Corps discret   GcdDomain.Field.domain.
  Lemme 4, Cor. 5 Content : cont_n, cont-div, cont-univ, cont-M ;
                  Bounded.prim-M (d | u e_i pour tout i, e primitif => d | u).
  Lemme 6         PolyGcd.PP (partie primitive) ; division d'un polynôme
                  par un scalaire non nul : PolyBase.Scalar (le quotient est
                  unique, donc obtenu sur le quotient depuis les listes).
  Lemme 7 Gauss   Gauss.gauss-list (listes), Gauss.GaussAt.gauss (A[X],
                  d /= 0) : induction directe de MRR sur la somme des
                  longueurs, en enlevant le coefficient constant (Gauss.Direct).
                  Product : d | coefficients(p q) => d | c(p)c(q).
                  content-mul-left/right : c(p q) et c(p)c(q) sont associés.
  Lemme 8         Gauss.DivPrim : E primitif, lambda /= 0, lambda f = E q
                  => E | f.
  Lemme 10        Elimination.elimination : record Elim (gd, lam, lam-nz,
                  div-f, div-g, common) ; récurrence primitive sur
                  n_f + n_g (Rec, onZero/onF/onG, Tops, Reduce) ;
                  pas de corps des fractions, pas de division euclidienne.
  Degré           Degree.deg : le plus petit majorant strict (DegF), une
                  proposition (deg-prop), donc obtenu sur le quotient.
  Intégrité       PolyGcd.integralP : Gauss.Direct.product avec d = 0 ;
                  c(p)c(q) = 0 contredit les deux contenus non nuls.


(d) Le pont vers Lambda_XYZ (Laurent3) : (S0)/(S1) pour P, Q quelconques.
    HomLambda.Over[A,G].Data[PL,QL,hP,hQ,m0,nP0,n0,nQ0,d,e,hPd,hQe] : pour
    A anneau à pgcd, PL, QL listes de termes à exposants >= 0 (Bsum = 0),
    homogènes de degrés d, e (HomPI), chacune avec un coefficient non nul,
      r, d', e', sum-P : r + d' = d, sum-Q : r + e' = e ;
      D0h, P'h, Q'h : listes homogènes de degrés r, d', e' (D0h-hom, ...),
        venant de D0 = pgcd(P,Q), P', Q' dans S = A[X][Y][Z] ;
      P-eq : D0h P'h = PL et Q-eq : D0h Q'h = QL dans Lambda (mulP) ;
      s0 : D0h f = 0, f à support fini  =>  f = 0                  (S0)
      s1 kW : la donnée S1T d'ACLCech.Data pour P'h, Q'h :
        al dans SL (kW + e'), be dans SL (kW + d'),
        P'h al + Q'h be = 0  =>  w dans SL kW, al = -Q'h w, be = P'h w.  (S1)
    S0S1.Over[k,...] : l'instance A = k[b][a], k corps discret.
    ACLInstance : les hypothèses pour les P, Q d'ACL §4.4 (listes PlP, PlQ
    de FixedCochain.ACL) se déchargent par calcul (refl).
    Étapes :
      Psi        psi : S -> Lau (coefficient de X^i Y^j Z^k ; 0 hors de N^3) :
                 additive, A-linéaire, X, Y, Z -> décalages, psi 1 = delta,
                 injective.
      Rep, Phi   liste canonique nl s (coefficients sous le degré, trois
                 niveaux ; une donnée, sans troncation), actN (nl s) 1 = s,
                 psi (s s') = mulP (liste de s) (psi s').
      Shift      un élément à support fini, décalé par X^K Y^K Z^K (K borne
                 les exposants négatifs de sa liste), est psi d'un élément
                 de S ; retour par le décalage inverse.
      Lambda     Reg (s /= 0 est régulier sur Lambda à support fini),
                 (S0), (S1) sans homogénéité ; w unique, donc extrait des
                 troncations de Fin.
      Degrees    Up n, Dn n (composantes nulles en degré >= n, < n) ;
                 Up-mul, Dn-mul.
      Homog      composantes homogènes comp n x dans S, témoin d'un
                 coefficient non nul, degrés extrêmes par recherche.
      HomDivisor composantes extrêmes d'un produit ; un diviseur d'un
                 élément homogène non nul est homogène.
      HomLambda  listes homogènes, projection hproj de w en degré kW.

3. FICHIERS
-----------

  GcdDomain     Div, GcdOf, GcdDomain, Domain (simplification), Gcd
                (lemme M, Euclide), Field
  Content       contenu d'une suite finie, corollaire 5
  PolyBase      A[X], coefficients (CharPoly.coef), Prim, Scalar
  Gauss         lemmes 7 et 8
  Elimination   lemme 10
  Degree        degré sur le quotient
  PolyGcd       théorème 11
  Iterate       corollaire 12
  Syzygy        proposition 14
  Psi, Rep, Phi, Shift, Lambda, Degrees, Homog, HomDivisor, HomLambda,
  S0S1, ACLInstance       le pont vers Lambda_XYZ (§2 (d))


4. LE RACCORD À ČECH (fait, dans sag/acl-zmt)
---------------------------------------------

Voir sag/acl-zmt/README.txt §7 : CechSections.Sec.F2D, CechZMTD0,
ACLGeneral (P, Q quelconques, conditionnel sur la présentation noethérienne
codée de A et les identités de degrés des cartes), ACLFinalGeneral (l'exemple
d'ACL par la voie générale, achevé).  Pour cela HomLambda.Data fournit aussi
P'h-poly, Q'h-poly (CechModules.IsPoly) et fP, fQ (P f = D0 (P' f)).
Renommage : GcdDomain.Field -> FieldGcd.

5. FIN DU PLAN (fait, sag/acl-zmt)
----------------------------------

  1. ACLGeneral : les identités de degrés des cartes sont dérivées de hPd,
     hQe ; seul conditionnel restant : la présentation noethérienne codée.
  2. ACLGeneralK : k[b][a], cartes quelconques, ACHEVÉ.
  3. ACLControlGeneral : D0 = Z + aX non inversible, ACHEVÉ.
  Hors périmètre : la réduction à une équation de Hensel (ACL 4.8-4.10).
