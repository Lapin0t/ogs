# Road map / journal

## Représenter les arbres de böhm (et leur bisimilarité).

On fait un type d'événements pour les arbres (la signature de l'arbre).

Piste (explorée): on peut prendre la signature des lambda-termes et au lieu de
construire l'algèbre initiale (les lambda-termes), on prend l'itree (les
lambda-termes potentiellements infinis). Comme les itree sont itératifs ont a
quand même un fold, donc on peut définir renommage/substitution sur les
lambda-termes infinis, puis enfin évaluation (toujours sur les termes infinis).
Pour l'évaluateur CBN on tombe sur les arbres de böhm. C'est mignon mais c'est
chiant de coder avec des récurseurs (au lieu de Fixpoint ou Equations).

## Lassen

En fait les arbres de Böhm sont CBN et au s'intéresse surtout à CBV
donc arbres de Lassen et bisimulation de forme normale
(eager-normal-form bisimulation). TODO ref.

Piste (à moitié exploré): 'normalement', la bisimilarité sur les
arbres de Lassen ne contient pas l'η-équivalence. En effet la
question est: qu'est-ce qu'on met dans les feuilles de
l'arbre: les valeurs, les variables ou rien du tout?

- Habituellement les seules feuilles sont des variables et dans ce cas
  la bisimilarité va distinguer f de λx.fx. En lambda-calcul pur
  non-typé, toutes les valeurs sont des fonctions, on peut donc
  décider d'η-développer les valeurs. On se retrouve alors avec des
  arbres strictement infinis (sans feuilles), dont la bisimilarité
  contient bien l'η-équivalence.

- Une autre approche est de changer la notion de bisimilarité sur les
  arbres pour esquiver la comparaison syntaxique des feuilles.  En
  effet à l'inverse de l'approche précédente, on peut décider que les
  valeurs soient des feuilles. L'équivalence up-to-tau sur les itree
  est paramétré par la relation voulue sur les feuilles. On va donc
  poser la relation coinductive (qu'on définirait avec paco):

  lassen_eqv x y := eutt (λ v1 v2 ⇒ lassen_eqv (exp_val v1) (exp_val v2))
                         (lassen x)
                         (lassen y)

  où  exp_val v := App (shift (term_of_val v)) (Var 0)

  Cette approche a un avantage théorique, dans le sens où à partir
  d'une fonction calculant l'arbre de lassen avec feuille-valeurs, on
  peut itérer la construction (avec exp_val au milieu) et reconstruire
  une fonction calculant l'arbre de lassen η-développé.

## On représente les LTS à 2 joueurs (qu'on appelle "dialogue")

## itree indexés

Que ce soit pour les arbres de böhm/lassen, les dialogues ou l'OGS, on a
souvent envie de contraindre plus les traces de nos itree, ie donner une
signature plus fine. Par exemple pour les arbres de lassen, si nos termes sont
bien scopés (et bien typés), on aimerait que les noeuds/événements fassent
apparaitre (et contraignent) les changements de contexte:

  lassen Γ (a ⇒ b) ∋ 'val' (lassen (Γ , a) b)
  lassen Γ t ∋ 'redex' (lassen (Γ , b) t)
                       (var Γ (a ⇒ b))
                       (lassen Γ a)

Autre exemple: pour les dialogues, on veut contraindre les traces à alterner
des événements joueur et opposant.

Pour cela, on va donc avoir un genre de LTS au niveau des types (à
creuser mais dans l'idée c'est un session-type, une description de
protocole). On va donner pour chaque événement l'index de départ
et l'index d'arrivée, et les traces seront alors contraintes à être des
séquences d'événements tels que les indices soient bien alignés. Tout
cela va être spécifié par:

  > l'ensemble des indices
  I : Type                    

  > l'ensemble des événements possible dans un certain indice de
  > départ
  qry : I → Type             

  > pour tout événement possible, l'ensemble des réponses (chaque
  > réponse donnant lieu à un sous-arbre)
  rsp : ∀ i, qry i → Type    

  > pour toute réponse (sous-arbre, donc), le nouvel indice courant,
  > ie la fonction de transition
  nxt : ∀ i (q : qry i), rsp i q → I

A partir de ces données, on peut calculer le foncteur associé
(l'"extension" du "conteneur indexé"):

  F : (I → Type) → (I → Type)
  F X i := ∃ q : qry i, ∀ r : rsp i q, X (nxt i q r)

On s'aperçoit que ce type ressemble très fortement à celui du constructeur 'VisF'
des itree: c'est la pair d'un événement q et d'une continuation k. Pour rappel,
dans les itree classiques, les arguments de VisF sont:

  VisF {R : Type} (q : E R) (k : R -> itree E X)

et le foncteur associé est donc:

  F X := ∃ R : Type, E R × (R -> X)

Ce F étant un genre de 'foncteur libre' sur E, pas très différent
d'une extension de Kahn à gauche (dans le cas où E est déjà un foncteur).

-- interlude sur la différence de représentation des événements non-indexés

La première différence entre cette représentation des événements par
un E : Type → Type et celle utilisée pour les événements dépendants
est la quantification existentielle sur Type. Le but étant de représenter
l'ensemble des requêtes et pour chaque requête l'ensemble des réponses, on peut
soit travailler avec
  req : Type
  rsp : req → Type
soit avec
  E : Type → Type
où E X est l'ensemble des requêtes ayant pour réponse X, ie la fibre de rsp en X.

Ainsi, si on peut voir

  Inductive freeer (E : Type → Type) (X : Type) : Type :=
  | Ret : X → freeer E X
  | Do {R} : E R → (R → freeer E X) → freeer E X

comme une 'free-er' monad sur E, on peut également la voir comme la monade libre
sur l'extension du conteneur représenté dans le style 'fibres' par E.

<<< fam vs pow
Ce choix est lié aux 2 représentations des sous-ensemble d'un ensemble X:

  fam X := ∃ Y : Type, Y ↪ X
  pow X := X → Prop

Un léger avantage d'utiliser fam plutôt que pow apparait lorsque l'on quantifie
sur les éléments du sous-ensemble:

  elems (Y , i : fam X) := Y
  elems (P : pow X) := ∃ X : Type, P X

On s'aperçoit que elems pour pow contient une quantification sur Type,
il s'agit donc d'un *grand* ensemble (un niveau plus haut que le
niveau de Type dans la hiérarchie), alors que cette montée de niveau n'apparait
pas dans la version fam.
>>> fam vs pow

Les extensions de conteneurs indexés sont strictement positifs en leur
argument, on peut donc en construire les algèbres initiales et
terminale. Les algèbres initiales sont les familles inductives que
l'on connait en Coq ou Agda (à ceci prêt qu'on ne peut pas forcer
d'unification des paramètres dans les constructeurs, on ne peut donc
pas exprimer l'égalité inductive, ou le type inductif des fibres d'une
fonction).
