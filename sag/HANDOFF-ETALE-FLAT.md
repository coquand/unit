# Platitude des présentations jacobiennes, modulo Noetheriannote

Date : 26 octobre 2026. Document de transmission ; les résultats nouveaux
décrits ci-dessous restent à formaliser.

## Mission et portée

Formaliser dans Unit le passage du relèvement de Taylor fini à la
platitude. Thierry autorise à laisser la partie noethérienne comme
hypothèse explicite, appelée ici `Noetheriannote`. Aucun fichier ou module
de ce nom n'a été trouvé dans `unit/` lors de la préparation : c'est le nom
proposé pour l'interface à écrire, pas une référence à un théorème existant.

Le premier objectif complet est le cas de deux équations en deux variables.
Pour tout anneau commutatif ensembliste A et F,G dans A[X,Y], poser

    J = F_X G_Y - F_Y G_X
    S = A[X,Y][1/J]
    B = S/(F,G).

Prouver, sous l'interface Noetheriannote décrite plus bas, que le A-module
sous-jacent à B est plat, au sens du critère des relations finies déjà
employé dans `chatelet/DescentFlat.seg`. Construire réellement S, B et les
morphismes. Les égalités sont des égalités dans les anneaux de polynômes
existants, pas des égalités de fonctions polynomiales.

Le théorème doit couvrir les anneaux arbitraires, le cas J=0 et l'anneau nul.
Ne pas imposer de décidabilité de l'égalité, de caractéristique particulière,
ni la propreté des idéaux engendrés par une suite régulière. L'inversibilité
de J est obtenue par localisation, pas ajoutée comme hypothèse sur A[X,Y].

Livrer d'abord ce cas. La généralisation à n équations et le passage aux
présentations lisses sont décrits à la fin comme suite du travail. Le seul
cas à deux variables ne doit pas être présenté comme une formalisation de
la platitude de tous les morphismes étales ou lisses.

## Répertoire et discipline de travail

- Racine : `/Users/coquand/CANONICITY/unit`.
- Créer `sag/etale-flat/`, son `All.seg` et son `README.md`.
- Réutiliser les sources par liens symboliques relatifs, comme dans les
  autres développements de `sag/`. Le `All.seg` doit être propre au nouveau
  développement, avec les imports en ordre de dépendance.
- Garder les autres développements et le checker en lecture seule pendant
  cette tâche. Ajouter les extensions et les adaptateurs dans le nouveau
  répertoire ; ne pas modifier indirectement une source via un lien.
- Conserver les paramètres habituels `univ`, `images`, `surjections`, et
  dériver `fe` comme dans `jacobian/All.seg`. Aucun axiome SAG n'est requis.
- Mettre toute hypothèse noethérienne dans un paramètre nommé de module ou
  dans un record d'interface passé en argument. Aucune déclaration sans
  corps ne doit masquer un lemme de platitude ou de régularité restant à
  prouver.
- Suivre `../seg/WRITING.md` depuis la racine `unit`. Écrire la
  preuve informelle courte avant les déclarations, utiliser les noms et
  interfaces existants, et examiner les ouvertures de définitions.
- Ne pas modifier `src/`, les règles de conversion, ni `tests.expected`
  pour obtenir l'acceptation d'une preuve. Ne pas committer.

## Sources à lire et acquis exacts

Les chemins de ce tableau sont relatifs à la racine `unit`.

| Source | Ce qui est disponible |
| --- | --- |
| `doc/jacobian-regularity.tex` | Preuve mathématique en deux variables ; le lemme 3.3 est le relèvement fini ; la réduction noethérienne n'est pas formalisée. |
| `sag/jacobian/README.txt`, `All.seg` | Périmètre exact et ordre des imports. |
| `sag/jacobian/FiniteJets.seg` | `Eq n p q` : égalité des coefficients de degrés strictement inférieurs à n ; `Change`, `bump`, `bump-change`. |
| `sag/jacobian/Bivariate.seg` | Expressions, évaluation dans une A-algèbre, dérivées, jacobien, Taylor au degré suivant. |
| `sag/jacobian/LinearSolve.seg` | Résolution du système 2 x 2 avec déterminant inversible. |
| `sag/jacobian/TaylorLift.seg` | `lift n : State n`, F=f-T et G=0 modulo T^(n+1). |
| `sag/jacobian/StableAnnihilator.seg` | `Stable f n` et `Kernel.result` : (f-T)p=0 modulo T^(n+1) implique p(0)=0 sous Stable. |
| `sag/jacobian/RegularAt.seg` | Application du relèvement à une véritable identité polynomiale FU=GV. |
| `sag/jacobian/JacobianDivisibility.seg` | FU=GV implique seulement, sous `NoetherianInput`, l'existence tronquée de e,W avec J^e U=GW. |
| `sag/jacobian/PolynomialIdentity.seg`, `BivariateNaturality.seg`, `ExpressionRepresentation.seg` | Anneau A[X][Y], transport des identités, naturalité, représentants par expressions. |
| `sag/jacobian/PrincipalQuotient.seg`, `PowerLocalization.seg` | Quotient principal et localisation, avec certificats de noyau. |
| `sag/polynomial/PolynomialRing.seg`, `Universal.seg`, `RingHom.seg` | Anneaux de polynômes effectifs et propriétés universelles. |
| `sag/pn/PolynomialCoefficients.seg` | Coefficients sur le quotient polynomial et extensionalité. |
| `sag/cffr/RegularIdeal.seg`, `QuotientRing.seg` | `IdealPred`, opérations sur les idéaux, quotient par un idéal propositionnel, projection et noyau. |
| `sag/chatelet/DescentFlat.seg` | `Over[A,setA].At[M].Flat` et `OneToMany` : le critère de relations finies à atteindre. |
| `sag/chatelet/DescentLinear.seg`, `DescentModuleMaps.seg` | Modules libres finis, sommes, combinaisons linéaires, passage d'une application linéaire à ses colonnes. |
| `sag/cokernel7/Modules.seg` | Modules sur `Ring.CRing`, via `RingBridge`. |
| `sag/cffr/Flat.seg` | Dénominateur commun et annulation par une puissance commune ; prouve la conservation d'une injection de modules libres finis par localisation. Ce fichier ne fournit pas à lui seul le prédicat général `DescentFlat.Flat`. |
| `sag/mertens/README.txt`, `ZeroProduct.seg` | Dedekind–Mertens univarié et conséquence d'annulation des coefficients. Le lemme multivarié de contenu n'est pas déjà disponible. |

Les dépendances transitives peuvent être nombreuses : vérifier les imports
réels et les types plutôt que supposer qu'un nom de fichier indique un
théorème utilisable directement. Ne pas recopier toute une bibliothèque.

## 1. Compatibilité des relèvements : petit premier résultat

La question reçue par email porte sur la compatibilité de x_N et x_(N+1).
Avec l'indexation du lemme 3.3, la formule exacte est

    x_(N+1) = x_N + a_N T^(N+1),
    y_(N+1) = y_N + b_N T^(N+1).

Donc la compatibilité est modulo T^(N+1), et implique celle modulo T^N.
Dans `TaylorLift.Step`, `cx.1` et `cy.1` sont déjà les preuves locales.
Exporter, dans une nouvelle enveloppe, les deux déclarations

    Eq (suc n) (lift n).1 (lift (suc n)).1
    Eq (suc n) (lift n).2.1 (lift (suc n)).2.1.

Ces lignes sont des spécifications schématiques : utiliser les vrais
préfixes de modules et accessors. La récursion de `lift` donne le lien
définitionnel avec `Step[n,lift n]`.

La divisibilité et la preuve de platitude proposée ici n'exigent aucune
série infinie : on utilise un seul ordre fourni par Stable.

## 2. Ce que Noetheriannote peut supposer

Séparer deux composants, dont les hypothèses restent visibles dans les
types finaux. On peut les regrouper dans un record `Noetheriannote` ; le
choix des univers et de la syntaxe exacte appartient à la formalisation.

### N : calcul noethérien abstrait

Un prédicat `Noeth` sur les anneaux commutatifs ensemblistes, avec :

1. stabilité par extension polynomiale ;
2. stabilité par quotient par un idéal de type fini (les idéaux principaux
   et les idéaux engendrés par les coefficients d'une relation suffisent) ;
3. stabilité par localisation en les puissances d'un élément ;
4. pour chaque anneau C muni de `Noeth C` et chaque c dans C,

       merely (N : Nat, StableAnnihilator.Over[C].Stable c N).

Les transports entre présentations isomorphes doivent être justifiés,
soit dans les adaptateurs, soit par une propriété explicite de l'interface.
Ne pas prendre en hypothèse « tout anneau est noethérien », ni la
stabilisation des annulateurs de tout élément de tout anneau.

Cette interface suffit pour prouver le premier théorème

    Noeth A -> Flat_A(S/(F,G)).

### D : réduction des données finies, pour enlever Noeth A

Le composant de réduction noethérienne porte sur des données et des
**identités polynomiales finies**, et non sur la conclusion de platitude.
Une forme spécialisée suffisante est la suivante.

Données : A, une liste finie a_i dans A, F,G,p_i,U,V dans A[X,Y], k dans N,
et l'identité

    J^k * sum_i a_i p_i = F U + G V                 (D1)

dans A[X,Y]. Le composant D fournit, sous troncation :

- un anneau commutatif ensembliste A0 avec `Noeth A0` ;
- un morphisme h : A0 -> A ;
- des a_i0, F0,G0,p_i0,U0,V0 dont les images sont les données précédentes ;
- l'identité correspondante (D1) sur A0, avec le même entier k et
  J0=Jac(F0,G0).

Il faut descendre les identités, pas seulement leurs coefficients. Le
morphisme h n'a pas besoin d'être injectif. Cette interface exprime la
réalisation d'un nombre fini de données et d'équations dans un anneau
noethérien ; sa preuve est la partie autorisée à rester en attente.

On peut demander des représentants par listes/expressions pour F0,G0 et
les autres polynômes. Leur interprétation doit être reliée aux vrais
anneaux de polynômes. La naturalité du jacobien est à prouver ou réutiliser.

Sous N et D, le résultat final n'a plus d'hypothèse `Noeth A`. Ne pas
s'arrêter au seul théorème sur une base noethérienne en l'annonçant pour
une base arbitraire. Inversement, ne pas mettre les syzygies, la régularité
ou la platitude dans les champs de Noetheriannote.

## 3. Régularité sur une base noethérienne

Pour C noethérien, poser R=C[X,Y], S=R[1/J]. Il faut établir :

    F régulier dans S ;
    G régulier dans S/(F).

On peut aussi établir l'autre ordre, mais un ordre suffit pour la suite.

### Régularité modulo une équation

La seconde assertion utilise `JacobianDivisibility` avec les équations
échangées. Le jacobien devient -J ; identifier les localisations en J et
-J, ou prouver un adaptateur par leurs propriétés universelles. N fournit
la stabilisation dans (C[X,Y]/F)[1/(-J)]. Passer des certificats polynomiaux
aux éléments localisés en choisissant des représentants et en chassant
les dénominateurs. Ne pas omettre ce passage.

### Régularité de F seul : éviter une hypothèse cachée

Le résultat actuel de divisibilité ne prouve pas à lui seul que F est
régulier. Une voie courte sous N est de généraliser le relèvement fini :
dans une C-algèbre E avec J(x,y) inversible, sans supposer G(x,y)=0,
construire

    F(x_N,y_N) = F(x,y)-T  modulo T^(N+1),
    G(x_N,y_N) = G(x,y)    modulo T^(N+1).

La matrice de correction est exactement celle de `TaylorLift`. Seule la
cible constante de G change. Mettre cette extension dans un nouveau
module et préserver le théorème existant.

Voici l'application avec dénominateurs explicités. Si F*(p/J^d)=0 dans S,
le critère de noyau fournit e tel que F*(J^e p)=0 dans R. Dans E=S,
substituer le relèvement dans cette véritable identité polynomiale.
On obtient (f-T)q(T)=0 modulo T^(N+1), où N est fourni par N pour f=F(x,y).
`StableAnnihilator.Kernel.result` donne q(0)=J^e p=0 dans S. J étant une
unité, p/J^d=0. C'est la régularité cherchée.

Cette voie ne dépend pas de la généralisation multivariée de
Dedekind–Mertens. Le contenu reste une autre preuve possible ; si elle est
choisie, son étape multivariée doit effectivement être démontrée.

## 4. Platitude élémentaire des polynômes et localisations

Définir éventuellement un certificat de platitude pour un morphisme
h:A->C, puis prouver son équivalence avec le prédicat existant `Flat` sur
le A-module sous-jacent à C. Le certificat requis est :

    sum_i h(a_i)b_i=0
      -> merely (m, c_ij dans A, y_j dans C,
           b_i=sum_j h(c_ij)y_j pour tout i,
           sum_i a_i c_ij=0 pour tout j).

Ce sont toutes les relations finies, pour tout nombre de termes. Une
propriété concernant seulement l'injectivité de matrices ne suffit pas.

- Polynômes : prendre une borne commune pour les supports des b_i,
  puis leurs coefficients comme c_ij et les monômes comme y_j. Pour
  A[X,Y], utiliser des supports finis à deux indices, ou prouver la
  transitivité de la platitude et appliquer deux fois le cas univarié.
- Localisation d'une A-algèbre plate C en j : écrire b_i=p_i/j^d avec un
  dénominateur commun. Une relation donne un e tel que
  `sum_i h(a_i)(j^e p_i)=0` dans C. Appliquer la platitude de C, puis
  diviser les y_j obtenus par j^(d+e). Ne pas supposer j régulier.

Les représentants et bornes communs sont obtenus par induction finie et
élimination de troncations vers une proposition. Pas de choix global de
représentants.

## 5. Le lemme central : correction des relations modulo un idéal

D'abord formaliser le petit lemme de syzygies dans un anneau C : si f est
régulier et g régulier modulo f, alors

    f u + g v = 0
      -> merely (w, u=g w, v=-f w).                (Syz)

Preuve : modulo f, g v=0, donc v=f t ; annuler f dans
f(u+g t)=0, puis prendre w=-t. Utiliser le vrai certificat de noyau du
quotient principal. Aucune division par f ou g.

Pour la platitude de B=S/(F,G), fixer une relation finie

    sum_i a_i b_i = 0 dans B.

Choisir des relèvements p_i dans S et un certificat

    sum_i a_i p_i = F u + G v.                    (R)

Poser I=(a_i) dans A et

    C=A/I,    S_C=C[X,Y][1/J_C].

Il faut construire la réduction rho:S->S_C et démontrer :

1. rho est surjective au sens tronqué ;
2. rho(z)=0 équivaut à l'existence tronquée de z_i dans S tels que
   z=sum_i a_i z_i ;
3. rho(F), rho(G), rho(J) sont les polynômes/jacobien sur C attendus.

Ce sont de vrais lemmes à prouver. Ils réunissent le quotient effectif
A/I, les coefficients polynomiaux, et la chasse aux dénominateurs. Ne pas
les laisser comme champs de l'interface noethérienne.

Dans le cas Noeth A, N donne Noeth C. Appliquer la section 3 à C.
La réduction de (R) est une syzygie, puisque les a_i s'annulent. Par (Syz),
choisir w_C avec rho(u)=G_C w_C et rho(v)=-F_C w_C. Relever w_C en w dans S.
Les certificats de noyau donnent des u_i,v_i dans S avec

    u-Gw=sum_i a_i u_i,    v+Fw=sum_i a_i v_i.

Poser p'_i=p_i-Fu_i-Gv_i. Alors

    sum_i a_i p'_i=0 dans S,
    p'_i a pour image b_i dans B.

Appliquer la platitude de S établie à la section 4, et envoyer le
certificat obtenu dans B. Cela donne exactement le critère des relations
finies pour B, sans Tor ni complexe de Koszul.

Pour situer le calcul : il prouve aussi

    IS intersect (F,G)S = F(IS)+G(IS).

Cette égalité d'idéaux peut être documentée, mais n'est pas un substitut
au théorème final de platitude dans le prédicat choisi par la bibliothèque.

## 6. Enlever Noeth A en utilisant D

Partir d'une relation finie dans B pour A arbitraire. Obtenir un
dénominateur commun pour les b_i : b_i=image(p_i)/image(J)^d, p_i dans R.
Utiliser le noyau du quotient et celui de la localisation pour construire
une identité de la forme (D1) dans R, avec U,V et k explicites sous
troncation. Le dénominateur commun d peut être conservé tel quel.

Appliquer D à toutes ces données. Dans

    B0=A0[X,Y][1/J0]/(F0,G0),

l'identité descendue implique `sum_i a_i0 b_i0=0`, où
b_i0=image(p_i0)/image(J0)^d. La section 5 donne un certificat de platitude
sur A0. Le morphisme h induit B0->B ; envoyer ses coefficients c_ij0 par h
et ses éléments y_j0 par B0->B. On obtient le certificat demandé sur A.

Ne pas faire appel à une affirmation non prouvée « la platitude descend
de A0 à A ». C'est le transport du certificat fini ci-dessus qui prouve
ici le résultat. Les morphismes polynomiaux, de localisation et de quotient,
avec leurs valeurs sur les générateurs, doivent tous être construits.

## 7. Organisation suggérée et livrables

Adapter les noms selon les interfaces réellement utiles :

| Fichier nouveau proposé | Contenu |
| --- | --- |
| `TaylorCompatibility.seg` | Compatibilité des relèvements existants. |
| `Noetheriannote.seg` | Types des interfaces N et D ; aucune preuve prétendue de ces hypothèses. |
| `TaylorTargets.seg`, `RegularPolynomial.seg` | Cible constante générale pour G, puis régularité de F seul sous N. |
| `RegularPair.seg`, `PairSyzygy.seg` | Régularité modulo une équation, puis (Syz). |
| `FlatRelations.seg` | Certificats explicites, module sous-jacent à une algèbre, pont avec `DescentFlat.Flat`. |
| `PolynomialFlat.seg`, `LocalizationFlat.seg` | Platitude sans hypothèse noethérienne. |
| `CoefficientQuotient.seg`, `PolynomialReduction.seg`, `LocalizedReduction.seg` | Réduction modulo (a_i), surjectivité et noyau exact. |
| `PairQuotient.seg` | B=S/(F,G), son morphisme, représentants et certificats de noyau. |
| `QuotientFlat.seg` | Correction d'une relation ; théorème générique à partir des syzygies modulo I. |
| `EtaleFlat2.seg` | Théorème sous Noeth A, puis théorème pour A arbitraire sous N et D. |
| `Examples.seg` | Spécialisations contrôlant les énoncés. |

Livrables : sources, `All.seg`, README donnant les noms publics exacts,
les hypothèses N/D exactes, les commandes et résultats de vérification,
et une preuve informelle courte correspondant à l'argument réellement
formalisé. Conserver ici une section de progression avec les obstacles
précis. Ne pas marquer comme terminé un théorème dont la conclusion a été
affaiblie ou dont une étape ci-dessus est devenue une hypothèse supplémentaire.

## 8. Vérification

Depuis la racine `unit`, utiliser le checker de ce dépôt :

```sh
cabal build exe:seg --offline
./segc sag/etale-flat changed
./segc sag/etale-flat all
```

Le checker a déjà un budget de 10 secondes par déclaration. Examiner les
diagnostics `--opened` pendant le développement ; expliquer les ouvertures
importantes et les éventuels dépassements. Exemple, avec seulement les
nouveaux modules sélectionnés pendant l'itération :

```sh
SEG=$(cabal list-bin exe:seg)
cd sag/etale-flat
timeout 55 "$SEG" All.seg --only EtaleFlat2 --opened
```

`--only` laisse les autres déclarations non vérifiées : le résultat final
doit aussi avoir un contrôle complet dans un processus frais, sans ce filtre :

```sh
# Depuis la racine unit ; SEG contient un chemin absolu.
SEG=$(cabal list-bin exe:seg)
cd sag/etale-flat
timeout 55 "$SEG" All.seg
```

Exemples utiles : F=X,G=Y ; F=X+X^2,G=Y ; F=0,G=Y (J=0, localisation nulle).
Ils peuvent conserver le paramètre Noetheriannote ; ne pas inventer une
instance de N/D pour faire tourner un exemple. Pour le relèvement,
réutiliser les calculs explicites de `jacobian/Examples.seg` et vérifier
la nouvelle compatibilité à quelques ordres. Les tests complètent la
preuve générique, ils ne remplacent pas les quantificateurs du théorème.

## 9. Suite : n variables et présentations lisses

Après livraison du cas deux variables : pour n équations F_i en n variables,
généraliser la correction de Taylor avec la matrice jacobienne inversible.
Pour montrer la régularité de F_i modulo les précédents, travailler dans

    (A[X_1,...,X_n]/(F_1,...,F_(i-1)))[1/J],

déformer F_i en f_i-T, et garder les autres valeurs F_j constantes.
La stabilisation et le même lemme tronqué donnent la régularité. La
première étape i=1 couvre la régularité individuelle nécessaire.

Remplacer (Syz) par le lemme : les syzygies d'une suite régulière sont
engendrées par `F_j e_i - F_i e_j`. Une preuve élémentaire par induction
sur la longueur suffit ; on peut aussi réutiliser un résultat exact de
`koszul/` s'il correspond à cette représentation. La correction modulo
(a_i), puis la réduction des données finies, donnent la platitude.

Pour r équations en n variables avec un mineur r x r inversible, prendre
les n-r autres variables dans l'anneau de base et utiliser la transitivité
de la platitude. Pour annoncer tous les morphismes étales/lisses, il faut
en plus une définition et le passage aux présentations locales, puis la
localité de la platitude. Ces étapes ne font pas partie du premier objectif.

## Progression

- 2026-10-26 : handoff écrit après lecture des sources ; aucune nouvelle
  preuve de platitude formalisée à ce stade.
- 2026-10-26 (suite) : premier objectif formalisé dans `sag/etale-flat/`
  (voir son README.md). Vérification complète dans un processus frais :
  `All.seg: 6211 declarations, 0 failed, 2.17 s` ; `./segc sag/etale-flat all` :
  108 modules, 0 échec. Théorèmes finaux :
  `EtaleFlat2.Over[A,setA,F,G].Noetherian[nc,noeth].{flat,module-flat}` (A
  noethérien) et `EtaleFlat2.Arbitrary[nn,A,setA,F,G].{flat,module-flat}` (A
  arbitraire, sous `nn : Noetheriannote`), au sens de `FlatRelations.Flat`,
  équivalent (`FlatRelations.Over.equivalent`) à `DescentFlat.At[...].Flat`.
  Compatibilité des relèvements : `TaylorCompatibility`. Hypothèses :
  uniquement les records `Noetheriannote.Calculus` (N) et
  `Noetheriannote.Reduction.Statement` (D). Écarts assumés : S/(a)S au lieu
  de C[X,Y][1/J_C] (même anneau, réduction = projection), (Syz) modulo
  (a)S, régularité de G modulo F par TaylorLift avec F, G échangés.
  Obstacle rencontré : une autre session a modifié `sag/jacobian` pendant le
  travail (`StableAnnihilator.Kernel`) ; adapté. Restent : preuves de N et D,
  cas n équations et présentations lisses (§9).
- 2026-10-26 (fin) : le théorème est maintenant **sans hypothèse** :
  `EtaleFlat2.Over[A,setA,F,G].{flat,module-flat}` pour tout anneau
  commutatif A. N et D ne servent plus : `RegularPair` réduit les deux
  régularités à un principe de noyau (`First.Zero`, `Second.Zero`), prouvé
  pour tout A dans `RegularCoded` par le sous-anneau codé et Hilbert sur Z
  (`sag/noetherian`, méthode de `doc/jacobian-noetherian.tex`, session
  canonicity-69). Vérification complète : `All.seg: 6742 declarations, 0
  failed, 2.31 s` ; `./segc sag/etale-flat all` : 121 modules, 0 échec. La
  voie conditionnelle (`Noetheriannote`, `Arbitrary`) est conservée.
  Reste : n équations et présentations lisses (§9).
