Cayley–Hamilton, endomorphismes et transport par univalence
27 octobre 2026

Les deux jalons sont vérifiés. Aucun axiome ajouté au contexte Theory
(univalence, images, surjectivité ; FunExt dérivée). Le vérificateur et
les bibliothèques existantes n'ont pas été modifiés par ce développement.

Preuve informelle : ../../doc/cayley-hamilton-univalence.tex et .pdf.
Programme initial : ../../doc/cayley-hamilton-univalence-handoff.txt.

1. RÉSULTATS

Pour A anneau commutatif en ensembles, n quelconque (y compris 0),
M libre de rang n et f : End_A(M) :

  EndCayleyHamilton.Over[A,setA,n].WithBasis[M,e]
    phi                       : M_n(A) ≃ End_A(M), isomorphisme d'algèbres
    package                   : paquet effectivement transporté par sip
    chi-coordinates f         : chi(f) = chi_matrix(phi^{-1}(f))
    based-cayley-hamilton f    : chi_matrix(phi^{-1}(f))(f) = 0
    on-vector f x             : la même identité appliquée à x

Ici e : A^n ≃ M est donnée. End_A(M) est construit indépendamment des
matrices, avec les applications linéaires pour porteur et la composition
pour multiplication. Les opérations additives sont celles de Lines.Hom.

  IntrinsicCharPoly.Over[A,setA].At[M,n,bM,f]
    chi                       : élément de A[T], sans base choisie
    Coordinates[e].comparison : chi = CharPoly.char n a_e
    monic                     : coefficient de degré n égal à 1
    bounded                   : tous les coefficients après n sont nuls

  CharPolyComparison.Over[A,setA].At[M,n,bM,f]
    Basis[e].transported-polynomial : le polynôme du paquet SIP est chi
    cayley-hamilton                 : chi(f) = 0 dans End_A(M)
    on-vector x                     : chi(f)(x) = 0
    basis-independent e e'          : les deux polynômes matriciels coïncident

Ici bM : FinFree M n = Trunc(LinEquiv M A^n) : aucune base choisie.
La monicité et la borne de degré conviennent aussi à l'anneau nul.
Aucune décidabilité de l'égalité ou hypothèse 1 ≠ 0 n'est utilisée.

  CharPolyNaturality.Over[A,setA].At[M,N,n,bM,bN,j,f].natural
    chi_N(j f j^{-1}) = chi_M(f), pour j : M ≃ N linéaire.

2. LE TRANSPORT EST RÉELLEMENT UTILISÉ

Chaîne de dépendances du théorème intrinsèque :

  MatrixCayleyHamilton.cayley-hamilton (bibliothèque existante)
    -> CHPackageTransport.Matrix.package
    -> CHPackageTransport.via-sip
         = transport de Package le long de AlgSIP.sip(phi)
    -> EndCayleyHamilton.WithBasis.package et cayley-hamilton
    -> CharPolyComparison.At.Basis.theorem
    -> CharPolyComparison.At.cayley-hamilton (élimination de bM).

Package(E) = (c : E.A -> A[T]) × ((t : E.A) -> eval_E(t,c(t)) = 0).
La première projection est une donnée. Son calcul est prouvé par
CHPackageTransport.path-value, sip-value et inverse-value ; il n'est
pas remplacé par une égalité entre preuves propositionnelles.

AlgTransportElements.move-iso est une induction sur les identités.
on-element utilise ensuite le lemme public AlgSIP.idToIso-sip.
PolyEvalTransport.path-eval, path-root et CHPackageTransport.path-value
sont également des inductions générales sur les identités, sans
induction sur les coefficients. sip reste opaque.
Le théorème général CayleyHamilton n'est pas réinstancié dans End(M)
pour contourner le transport ; il intervient par son client matriciel.

3. ADAPTATION DU SECOND JALON

Le handoff proposait det(T id - f[T]) sur A[T] ⊗_A M. On utilise ici
le module dual polynomial canonique D(M) = Hom_A(M,A[T]) et

  chi_M(f) = DetEnd(T id_D(M) - f*),   f*(lambda) = lambda ∘ f.

ScalarDual définit Hom_A(M,B) comme B-module pour tout morphisme A -> B,
indépendamment des bases. ScalarDualBasis construit, à partir d'une base
e : M ≃ A^n, une base de Hom_A(M,B), avec les deux inverses prouvés :

  lambda |-> (lambda(e^{-1}(e_j)))_j ;
  (p_j)_j |-> [x |-> Σ_j h(e(x)_j) p_j].

Pour B=A[T], la matrice du pinceau T id-f* est la transposée de TI-a_e.
IntrinsicCharPoly.Coordinates.entry et matrix-eq établissent cette identité.
La comparaison utilise les véritables DetEnd.delta-coords et
ExteriorTranspose.det-transpose, puis la définition de CharPoly.char.
Il ne s'agit pas d'une définition par choix d'une base ou par simple
descente du polynôme matriciel. Le scalaire déterminant est celui de
l'action sur la puissance extérieure supérieure déjà construite par DetEnd.

La précomposition est contravariante : elle ne fournit pas ici un
isomorphisme des algèbres d'endomorphismes. La transposition est traitée
au niveau du déterminant, où son invariance est déjà prouvée.

Une comparaison avec une construction tensorielle séparée de A[T] ⊗_A M
n'est pas formalisée. Elle n'est pas nécessaire aux résultats ci-dessus.
Le développement ne traite pas les modules projectifs non libres.

4. EXEMPLES

Examples.ZeroRank : polynôme 1 ; l'identité du module nul est nulle.
Examples.OneRank[c] : polynôme T-c et annulation transportée.
QuadraticPolynomial.At[u,v,w,z].formula : pour [[u,v],[w,z]],

  chi = (uz-vw) + T (-(u+z) + T).

Examples.TwoRank[u,v,w,z,M,e].quadratic x :

  f(f(x)) + (-(u+z)) f(x) + (uz-vw) x = 0,

où f est l'image de cette matrice par l'isomorphisme associé à e.
Les quatre coefficients sont arbitraires, sans hypothèse de symétrie.

Examples.Shear[c] : e(x,y)=(x+cy,y), inverse e(x,y)=(x-cy,y).
forth et back vérifient les inverses ; conjugation donne la fonction
explicite e ∘ f ∘ e^{-1} ; Intrinsic[f].invariant applique la naturalité.

5. VÉRIFICATION ET COÛT

Depuis unit :
  ./segc sag/ch-univalence all
Résultat : 185 modules (All inclus), 0 échec, 4,30 s.

Vérificateur en processus frais, depuis sag/ch-univalence :
  ../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg

Trois entrées pour séparer les couches, avec les mêmes imports de bibliothèque :
  Libraries.seg : 7 820 déclarations, 0 échec, 4,10 s.
  Stage1.seg    : 7 968 déclarations, 0 échec, 4,10 s.
  All.seg       : 8 229 déclarations, 0 échec, 4,48 s.
Donc 148 déclarations ajoutées pour le premier jalon et 409 au total,
avec les exemples. Les temps sont des mesures ponctuelles, dominées
par les bibliothèques ; leur différence ne mesure pas précisément le
coût propre des transports. Les nombres de déclarations incluent les
paramètres et alias suivant le comptage du vérificateur.

Code nouveau : 15 fichiers .seg, 602 lignes, commentaires et lignes vides
compris, hors les trois fichiers d'entrée. Répartition :
  105 lignes : EndAlgebra, AlgIsoOps, MatrixEnd, EndConjugation ;
   73 lignes : transport général et paquet matriciel ;
   23 lignes : client EndCayleyHamilton ;
  228 lignes : module dual, déterminant intrinsèque, comparaison, naturalité ;
  173 lignes : polynôme quadratique et exemples.
169 fichiers de bibliothèque sont des liens relatifs vers les sources
existantes. Aucun de ces fichiers n'a été copié ou modifié.

6. COMMENTAIRES SUR L'EXPÉRIENCE

Le premier client est court : le travail spécifique est la construction
de l'isomorphisme, tandis que le transport du paquet est général.
Les lemmes move-iso/on-element, path-eval, sip-root et les calculs de
fonctions transportées sont réutilisables pour d'autres assemblages.

Les points d'interface rencontrés :
  - Ring.CRing et Alg73.CRing : réutilisation de Modules/RingBridge ;
  - matrices par lignes et par colonnes : adaptation explicite ;
  - lois de linéarité : Lines.lin-eq et leur caractère propositionnel ;
  - Alg est dans U l+ ; les familles vers U l ont été eta-développées
    lors de leur passage à Prelude[l+].subst ;
  - accès aux alias des modules parents : alias explicitement introduits ;
  - déterminant intrinsèque et données sous troncation : réutilisation
    de DetEnd, puis élimination de la base uniquement dans des propositions.

Le pont CharPolyComparison.Basis.coordinates passe par refl : les inverses
explicites des équivalences produisent les bonnes coordonnées par conversion.
Ceci est distinct du calcul du transport par sip, qui reste propositionnel.
Aucun déroulement de la preuve opaque de SIP ni nouveau mécanisme de
conversion n'a été nécessaire. Il n'y a pas eu de comparaison avec une
seconde implémentation complète sans univalence, ni de test à l'échelle FLT.
