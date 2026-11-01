Contrôle fini d'un complexe filtré : certificats explicites
=========================================================

27 octobre 2026. Note : doc/filtered-cohomology.tex.

Contrôle indépendant du serveur, depuis ce répertoire :
  ../../dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg All.seg
Résultat : 2831 déclarations (bibliothèques comprises), 0 échec.
Les fondations de Theory sont celles des autres développements :
univalence, images et la propriété universelle des surjections.
Les fichiers de bibliothèque sont des liens relatifs vers acl-zmt.
Aucun fichier de ces bibliothèques n'a été modifié.

PORTÉE EXACTE
-------------
Théorème CONSTRUCTIF CONDITIONNEL aux données de génération finie.
AUCUNE hypothèse de noethérianité ni de cohérence dans les nouveaux
lemmes. Les paramètres generation supposent, pour une famille et une
borne fixes, une preuve de décomposition pour TOUTES les entrées
concernées, éventuellement sous troncation. Ils ne sont pas construits.
Il n'y a PAS d'application de ce nouveau théorème à ACL/ZMT ou étale-flat
avec ces paramètres déchargés. Principal.Finite reste conditionnel.

Ce n'est PAS une formalisation de l'implication classique :
  A noethérien + module de Rees de cohomologie fini
     => le sous-module gradué des classes devenant nulles est fini.
La noethérianité constructive codée disponible ne donne pas à elle seule
des générateurs d'un sous-module arbitraire.
Elle est définie par Span.Over.Noeth = Bar.Over[K,Good].Bars nil :
un arbre inductif bien fondé attestant une barre de listes bonnes,
avec coefficients codés. CodedNoetherian ajoute la surjectivité sous
troncation de l'interprétation des codes. Le rappel classique de la note
emploie, lui, « tout idéal est de type fini », en logique classique.

La cohérence constructive pourrait fournir des générateurs de noyaux
entre modules explicitement de présentation finie. De telles
présentations sur l'anneau de Rees ne sont pas fournies ici. La cohérence
de la base seule ne suffit pas au relèvement filtré : la note donne un
contre-exemple avec un anneau de valuation de rang deux.

On travaille directement avec des représentants et des égalités modulo
un bord, sans définir des quotients H^q ni construire un anneau de Rees.
La génération à chaque entrée peut être fournie sous troncation.

FilteredControl.seg
-------------------
ScalarFiltration : prédicats J_n(r), avec J_(k+n) contenu dans J_n.
Filtration : prédicats F_n(M), stables par somme et opposé, décroissants,
  avec J_n(r) => r*x dans F_n(M) pour tout x.
Les puissances d'un idéal quelconque satisfont ces conditions.

Generator[A,M,c] : valeur, degré e, écart g et certificat e+g=c.
Ce record contient des ÉTIQUETTES de degré, pas une preuve d'homogénéité
de sa valeur. Pour Kernel, e est le degré du bord d(b), et non de b.
Le lien avec une génération graduée est la donnée Rep/generation.

Family.small : les coefficients J_(g_i+m) deviennent des coefficients J_m.
Family.In.sum-in : une combinaison de ce type appartient à F_m(M).

Control : d:C0->C1 linéaire, filtration F0 sur C0, borne c.

  Image.Rep(m,x) : une liste FIXÉE de représentants de cycles z_i,
    des coefficients r_i dans J_(g_i+m), et v dans F_(c+m)(C0), avec
      x = somme r_i z_i + d(v).
  Image.control : même classe, avec coefficients dans J_m.
  UniformImage.image-control : énoncé pour tous les cycles d'ordre c+m,
    à partir de la fonction de génération (seulement sous troncation).

  Kernel.Rep(m,x) : une liste FIXÉE de primitives b_i,
    des coefficients r_i dans J_(g_i+m), et v dans F_(c+m)(C0), avec
      x = somme r_i d(b_i) + d(v).
  Kernel.control : w = somme r_i b_i + v appartient à F_m(C0), d(w)=x.
  UniformKernel.kernel-control : le même résultat pour tout bord d(z)
    d'ordre c+m, à partir de la génération du sous-module des classes
    nulles (sous troncation).
  UniformKernel.lift : il existe sous troncation h fermé avec
      h-z dans F_m(C0).

  UniformImage.Kill.vanish : si J_1 annule les cycles et si d=0,
    tout cycle d'ordre c+m+1 est nul. C'est l'application en degré zéro.

TwoGenerated.seg
----------------
Over[A,a,b] : instanciation des filtrations par IdealPowers pour I=(a,b).
Le cas principal est inclus avec b=0.
Principal[A,setA,f,c].Finite[gs,closed,generation].vanish :
  f*x=0 et x dans (f)^(c+m+1) => x=0,
  sous les données de génération du module gradué d'annulation filtrée.

CE QUI RESTE POUR LE THÉORÈME CLASSIQUE COMPLET
----------------------------------------------
1. Construire les données de génération à partir de présentations
   effectives de la cohomologie graduée et de son sous-module noyau,
   ou adopter des hypothèses constructives qui les fournissent.
2. Relier ces données aux représentations exactes utilisées dans les
   preuves ACL et étale-flat. Ces preuves existantes ne sont pas modifiées.
3. Pour un idéal avec un nombre quelconque de générateurs, instancier
   ScalarFiltration/Filtration avec une bibliothèque de puissances
   correspondante. Le calcul abstrait n'est pas limité à deux générateurs.

Les preuves actuelles de Kill et de correction finie utilisent moins :
une dépendance sur les suites effectivement rencontrées, sans fournir
la borne uniforme c. Le présent résultat ne remplace donc pas ces preuves
par un appel implicite à un Artin-Rees constructif uniforme.
