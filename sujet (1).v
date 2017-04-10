(** ** Coq : Une petite introduction *)

(** Il est possible de générer un fichier HTML à partir de celui-ci. Cependant je vous conseille de lire ce fichier dans votre éditeur de texte afin de pouvoir directement interagir avec Coq. L'objet de ce TP est de vous présenter les fondements du logiciel Coq et qu'à la fin, vous soyez à l'aise pour faire des preuves assez simples. *)

(************************)
(** * I : Introduction **)
(************************)

(** ** 1. 3 langages différents **)
(*********************************)

(** L'outil Coq regroupe trois langages distincts :
- Galina, le langage des termes
- Le vernaculaire, le langage des commandes
- Ltac, le langage des _tactiques_

Au sein d'un développement Coq, on manipule ces trois langages un peu en même temps. Pour prouver un développement, Coq se base sur un _type checker_. Toute la confiance de nos développements en Coq repose sur ce type checker. Cependant ce type checker n'existe que pour le langage Galina. Ce qui veut dire que tout développement Coq se ramène _in fine_ à type checker des termes dans le langage Galina. Le vernaculaire et Ltac sont des _méta-langages_ qui permettent de nous faciliter la vie et d'interagir avec l'outil.

Coq se base sur l'isomorphisme de Curry-Howard aussi appelé _propositions as types principle_. C'est à dire que prouver un énoncé A (écrit en Galina) revient à écrire un programme f dont le type est A.
En général, un tel terme f peut-être gros et pénible à écrire. Pour pallier à ce problème, on utilise un langage de tactiques. En combinant des tactiques, ce dernier nous permet de générer un terme f qui aura (on l'espère) le bon type.

La logique derrière Coq s'appelle le calcul des constructions inductifs. Cependant, dans le cadre de ce cours, on ne s'intéressera pas vraiment à la logique sous-jacente de Coq. On va seulement utiliser Coq comme un outil pour nous permettre de prouver nos programmes.

Enfin, le vernaculaire est un langage de commandes. C'est par exemple en utilisant le vernaculaire que l'on va indiquer à Coq qu'on est en train de définir un théorème, un lemme, ou bien on est entrain de créer une fonction. On intéragira toujours avec Coq grâce au vernaculaire. Voilà pour le point théorique, passons maintenant à la pratique.
 *)

(** ** 2. Types en Coq **)

(** Objectif :
    - introduction aux commandes Check, About Print.
    - introduction aux entiers en Coq
 *)

(** La commande Check (faites attention à la casse) prend en entrée un terme et s'il est bien typé, affiche son type. Toute commande en Coq se termine par un point. *)

Check 3.

(** Le type de 3 est nat. En Galina, les types sont aussi des termes (une conséquence des types dépendants *)

Check nat.

(** Set est ce qu'on appelle une _sorte_. Une _sorte_ est un type dont les éléments sont eux-mêmes des types. Par exemple, le type bool est aussi dans Set *)

Check bool.

(** Il existe plusieurs sortes en Coq. On peut distinguer trois sortes en Coq : Set, Prop et Type. La sorte Prop est le type des propositions. *)

Check (forall x, x = x).

(** Il se trouve que les sortes ont eux-même un type *)

Check Set.

Check Prop.

Check Type.

(** On peut résumer cette hiérarchie de types par le schéma suivant (merci Lucca) :
<<
                 Type
               /      \
            Set       Prop
           /  |      /    \
        nat  bool  True  ((1=0) \/ False)
       / |   /  \
      1  0  true false
>> *)

(** Afin de vous éviter des détails logiques, Coq vous ment un peu dans son affichage. En général, c'est pour notre bien, mais parfois cela peut-être gênant. Ainsi, si Type n'est pas vraiment une sorte, c'est Type 0 qui en est une. De plus, le type de Type 0 c'est Type 1. Pour s'en apercevoir on peut utiliser le vernaculaire *)

Set Printing Universes.

Check Set.

Check Prop.

Check Type.

Unset Printing Universes.

(** Au lieu d'utiliser la commande Check pour les types, il est aussi possible d'utiliser la commande About qui donne un peu plus d'informations *)

About nat.

(** Cependant, cette dernière ne fonctionne pas pour les sortes *)

(* About Prop. *)

(** On peut aussi vouloir afficher la définition d'un type ou bien d'une fonction. Pour cela on utilise la commande Print *)

Print nat.

Print plus.

Print Nat.add.

(** En conclusion :
    - En Coq n'importe quel terme a un type
    - On distingue les types des données comme nat, bool, avec le type des propositions (1 = 2, True)
    - Set est la sorte qui contient les types pour les données, tandis que Prop est la sorte des propositions
    - Pour connaître le type d'un terme on utilise Check ou About (cette dernière est préférable en général)
    - Pour connaître la définition d'un type, d'une fonction on utilise la commande Print
 *)

(** ** 3. Librairies et notations **)

(** Objectif :
    - Introduction au système de module de Coq et la gestion des noms
    - Introduction aux commandes Require Import et Locate
 *)

Print nat.
(** Quand tout à l'heure, on a exécuté la commande Print nat, on a vu que ce dernier avait une définition (on verra ce que veut dire le mot-clé inductive plus tard) :
<<
Inductive nat : Set :=  O : nat | S : nat -> nat
>>

Donc on peut en conclure que que les entiers ne sont pas primitifs en Coq. Heureusement, le logiciel est bien fait et nous permet d'écrire nos entiers en base 10 comme on a l'habitude, mais derrière le terme est bien unaire. On peut le vérifier ainsi :
 *)

Set Printing All.

Check (S 0).

Check (1 = S 0).

Unset Printing All.

(** Par défaut, Coq vient avec toute une librairie. C'est le cas des connecteurs logiques entre autres. *)

Print or.

Print and.

(** Pour importer d'autres librairies en Coq, on utilise la commande Require Import *)

Require Import List.

(** C'est un peu l'équivalence de la commande open en OCaml. Cependant, vous vous apercevrez par la suite qu'il peut très rapidement y avoir des conflits de noms. Afin qu'il soit plus facile de lire des définitions ou bien des formules mathématiques, Coq utilise un système de notation. Ainsi on écrit en général True /\ True plutôt que and True True : *)

Check (True \/ True).

Check (or True True).

(** Pour voir à quel symbole est associé une notation, on utilise la commande Locate qui prend en argument une chaîne de caractères. *)

Locate "\/".

(** La commande Locate nous indique aussi le scoping de la notation. En effet, la définition de plus sur les entiers est différente de celle sur les réels. Pourtant, on voudrait garder la même notation. Le scoping permet donc de lever cette ambiguïté. Par exemple pour la notation + il y a plusieurs définitions *)

Locate "+".

(** Pour préciser le scoping d'un terme t, il faut préciser le scope en ajoutant un % derrière le symbole : (t)%scope *)

(** Conclusion :
    - Require Import fonctionne comme le Open d'OCaml
    - Les librairies introduisent de nombreuses notations.
    - Pour connaître la définition d'une notation, on utiliser la commande Locate
    - La même notation peut-être rattachée à plusieurs définitions
    - Coq résoud ces conflits en utilisant la notion de scoping (parfois appelé namespace)
 *)

(** ** 3. Des preuves simples *)

(** Objectif :
    - Introduction au mode de preuve interactif
    - Introduction aux tactiques : intro(s), apply, assumption, easy, reflexivity, exact
 *)


(** Passés ces détails techniques de Coq, intéressons-nous au monde de la preuve en Coq. Il existe deux façons de faire des preuves en Coq, soit on donne le terme et le type directement, soit on utilise le mode intéractif pour construire la preuve à l'aide de tactiques. Le mot-clé Definition permet d'associer un nom à un terme t dont le type est A. C'est une façon de faire pour construire une preuve en Coq : *)

Definition trivial0 : 1 = 1 := eq_refl.

(** Coq nous indique qu'il est content avec le message "trivial is defined". Ici on a donc trivial qui est un programme dont le type est 1 = 1. On a donc construit un terme de type 1 = 1, autrement dit on vient de prouver 1 = 1. Pour cela, on a utilisé eq_refl. On reviendra sur eq_refl un peu plus tard, c'était juste pour vous donner un exemple de la construction d'un terme. De façon général, derrière le symbole ":" on met un type, ici 1 = 1, et après := on met une définition ici eq_refl. Pour le mode interactif, on utilise en général d'autres commandes comme Lemma ou Theorem. Pour dire à Coq que l'on commence une preuve, ces commandes sont suivies de la commande Proof *)

Lemma trivial1 : 1 = 1.
Proof.


  (** On s'aperçoit alors que Coq change de mode. C'est le mode interactif qui permet de construire des termes. En dessous de la barre se trouve le _goal_, tandis qu'au dessus se trouve _le contexte_ (ici il est vide). Maintenant, Coq attend une tactique. Coq vient par défaut avec de nombreuses tactiques et il est possible d'en définir soi-même (même si on ne le fera pas durant ce cours). Pour des cas aussi simples il existe plusieurs tactiques. *)
  auto.

  (** Ici, Coq nous indique qu'il a résolu les buts et donc que la preuve est finie. auto est une tactique un peu magique qui résoud de nombreux goals. Cependant, dans le cadre de ce cours, je vous interdis de l'utiliser. Cette commande est un peu magique et on ne comprend pas forcément comment elle fonctionne. Il y a toujours une façon de se passer d'auto. Dans un but pédagogique, on va restart la preuve pour voir d'autres tactiques. *)

  Restart.

  reflexivity.

  (** La tactique reflexivity permet de résoudre des buts de la forme x = x, ce qui est notre cas. Dans Emacs ou bien CoqIde, cette tectique est coloriée en rouge. Cela veut dire qu'elle résoud un but et que si elle n'y arrive pas elle échoue. Par exemple tentez la tactique suivante (en enlevant la commande Fail) *)

  Fail contradiction.

  (** il existe une autre tactique un peu plus général -- easy -- qui permet aussi de résoudre ce but *)

  Restart.

  easy.

  (** Pour indiquer à Coq que l'on a fini une preuve, on utilise la commande Qed. *)
Qed.

(** Pour l'instant on a vu comment résoudre un but de la forme x = x, mais on ne va pas aller très loin ainsi. On va voir comment résoudre des propositions contenant des implications et des forall. *)

Lemma trivial2 : forall (x:nat), x = x.
Proof.

  (** pour prouver un but contenant un forall en tête, on utilise la tactique intro. On peut donner un identifiant au paramètre introduit *)
  intro x.

  (** On s'aperçoit que la tactique introduit a réussi car elle nous a ajouté x dans le contexte. On peut maintenant conclure la preuve. *)

  easy.

Qed.

(** Regardons avec l'implication maintenant. *)

Lemma trivial3 : forall (P:Prop), P -> P.
Proof.
  intro P.

  (** Pour introduire la flèche, on peut réutiliser la même tactique intro *)

  (** A noter qu'il est possible de combiner de faire plusieurs introductions en une seule fois avec la tactique intros. *)
  intro H.

(** Maintenant on se retrouve à vouloir donner un terme de type P. Heureusement on a un dans notre contexte, c'est H. On peut utiliser la tactique assumption pour dire à Coq d'utiliser H sans avoir besoin de mentionner l'hypothèse. *)

  assumption.

  (** On peut aussi utiliser la tactique exact pour préciser spécialement l'hypothèse à utiliser *)

  Undo.

  exact H.
Qed.

(** A ce stade, pour souligner l'utilisation de Curry-Howard, il peut-être intéressant de regarder les termes que l'on a définis. *)

Print trivial0.

Print trivial1.

Print trivial2.

Print trivial3.

(** On remarque en regardant le type de trivial3, que l'introduction de l'implication et du pour tout se traduisent tous les deux par une "abstraction", c'est à dire en construisant une fonction. La différence se fait seulement au niveau du type. En fait, dans la théorie de Coq (et de façon plus générale quand on a affaire aux types dépendants, l'implication est un cas particulier du pour tout). *)

(** Enfin, on va voir l'utilisation d'une dernière tactique : apply qui va nous permettre de prouver le théorème suivant : *)

Lemma trivial4 : forall (A B:Prop), (A -> B) -> A -> B.
Proof.
  intros A B H a.

  (** Comment on construit un terme de type B ? Pas le choix il faut utiliser H ! Cependant, il y a deux façons de le faire : en forward reasonning ou en backward reasoning. En forward reasoning on voudra faire nos manipulations dans le contexte et fabriquer un terme de type B. Pour se faire on peut utiliser la règle du modus ponens et dire si j'ai du A et du A -> B, alors je peux construire du B. *)
  apply H in a.

  (** Coq nous dit alors qu'à partir de a : A je peux construire un type b : B. Dans notre cas, il fait le remplacement directement au sein du terme a. A l'inverse, en backward reasoning, on va appliquer H au goal directement *)

  Undo.

  apply H.

  (** Cette fois, Coq nous demande de lui donner un terme de type A, que l'on a directement depuis le contexte, on peut donc conclure *)

  assumption.
Qed.

(** Avec ce petit ensemble de tactiques, vous pouvez vous exercez à prouver les formules suivantes. Remplacez le Admitted par votre preuve *)

Example example0 : forall A B, A -> B -> A.
Admitted.

Example example1 : forall A, A -> A -> A.
Admitted.

Example example2 : forall A B C, (A -> B -> C) -> A -> B -> C.
Admitted.

Example example3 : forall A B C (H:A -> B -> C) (HA:A) (HB:B), C.
Admitted.

Example example4 : forall n, (forall m, m = 0) -> n = 0.
Admitted.

Example example5 : (forall P, P) -> False.
Admitted.

(** Conclusion :
    - Le mode de preuve interactif permet de construire un terme de preuve pas à pas
    - On construit un terme de preuve en combinant un ensemble de tactiques
    - La tactique intros permet d'introduire dans le contexte la prémisse d'une implication mais aussi la variable d'un forall
    - Une tactique peut échouer si on ne l'applique pas correctement
    - Les tactiques en rouge sont des tactiques qui résolvent à coup sûr un goal ou bien échouent
    - Pour prouver un goal B à l'aide d'une hypothèse A -> B, on utilise apply
    - Il existe plusieurs façons de construire des preuves en Coq, certaines sont plus intuitives que d'autres
 *)

(** ** 4. Raisonner avec l'égalité *)

(** Objectifs :
    - Introduction à la notion de calcul en Coq
    - Introduction à la commande Eval ... in ...
    - Introduction aux tactiques simpl,rewrite, subst, clear et pose proof
    - Introduction aux tacticielles now ...
    - Introduction à la recherche de théorèmes en Coq *)


(** L'égalité à un statut très particulier en Coq. En particulier ce n'est pas la même que l'égalité d'Ocaml : *)

Example equality : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.

(** En Coq, il existe 4 notions différentes de calcul. La notion de calcul est profondément ancrée dans Coq. C'est ce qui fait que l'égalité de Coq est plus _puissante_ que celle d'OCaml, car en Coq l'égalité va utiliser la notion de calcul intégrée en Coq. Ceci est possible car Coq n'est pas Turing-Complet : tout calcul termine ! Comme le cacul termine toujours en Coq, pour tester l'égalité entre deux termes a et b, Coq va chercher à _réduire_ (en calculant) un maximum a et b et vérifier que leurs _formes normales_ sont structurellement égales. Comprendre comment un terme va se réduire n'est pas évident au premier abord et demande de la pratique. *)

(** En général, on ne fait pas de distinction entre les différentes notions de calcul. Pour demander à Coq de calculer, on peut utiliser la commande Eval compute in *)

Eval compute in (2 + 2).

(** compute est une _stratégie de réduction_ qui englobe les 4 notions de calculs. Il existe cependant d'autres stratégies de calcul qui pour nous auront peu d'intérêt. *)

(** Voici un exemple simple pour vous montrer un des pièges de l'égalité en Coq : *)

Example trivial5 : forall n, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Example trivial6 : forall n, n + 0 = n.
Proof.
  intros n.
  Fail reflexivity.
Abort.

(** 0 + n se réduit naturellement vers n, mais ce n'est pas le cas de n + 0. Cela dépend de la façon dont on a définit la fonction plus, on verra ça dans la suite de cette introduction. *)

(** On va voir maintenant comment utiliser des égalités en sein de nos preuves. Par exemple si j'ai dans mon contexte une égalité A = B et que mon goal c'est A, je voudrais pouvoir l'utiliser pour réécrire mon goal en B *)

Lemma trivial7 : forall n m, n = m -> S n = S m.
Proof.
  intros n m R.

  (** pour réécrire n en m, on utilise la tactique rewrite *)

  rewrite R.

  (** cependant, on aurait pu vouloir réécrire m en n. Cela se fait aussi avec rewrite *)

  Undo.
  rewrite <- R.

  reflexivity.
Qed.

(** par défaut rewrite écrit de gauche à droite. *)

Lemma trivial8 : forall n m, n = m -> n + S n = m + S m.
Proof.
  intros n m R.

  (** now est une tacticielle : elle prend en paramètre une autre tactique. On peut voir now H comme un raccourci pour H. easy. *)
  now rewrite R.
Qed.

(** il peut arriver à un moment dans l'élaboration d'une preuve d'avoir plusieurs égalités de la forme :
x1 = t1, x2 = t2, ... , xn = tn . Pour éviter d'avoir à écrire n fois rewrite et surtout de nommer à chaque fois les hypothèses, on peut utiliser la tactique subst qui va faire ça à notre place. *)

Lemma trivial9 : forall n1 n2 n3 n4, n1 = n2 + n2 -> n2 = n3 + n3 -> n3 = n4 + n4 -> n1 = 8 * n4.
Proof.
  intros n1 n2 n3 n4 R1 R2 R3.
  subst.

  (** A noter que subst fonctionne si l'un des deux membres de l'égalité est une variable. *)

  (** Cependant, il n'est pas possible de conclure directement car Coq n'arrive pas à voir que les deux membres sont égaux. Cela peut se voir en réduisant le membre droit à l'aide de la tactique simple. *)

  simpl.

  (** simpl est une tactique très pratique qui comme son nom l'indique permet de simplifier des buts. Comment on va dire à Coq qu'il est possible de résoudre ce but ? On va utiliser des lemmes. Heureusement ils ont déjà été prouvés pour nous. Mais comment trouver le nom de ces lemmes ? Pour cela on va utiliser la commande Search. Cette commande prend ou bien un nom en paramètre, ou bien un _pattern_.  *)

  Search "plus".
  Search "add".
  Search (_ + 0).
  Search (_ (_ + _) = (_ + _) + _).

  (** les deux lemmes dont on a besoin sont donc plus_n_O et PeanoNat.Nat.add_assoc . Il est possible de les inclure dans le contexte en utilisant la commande pose proof. *)

  pose proof plus_n_O.
  pose proof PeanoNat.Nat.add_assoc.

  (** Quand il y a un forall dans une hypothèse, alors de deux choses l'une :
      - soit Coq peut deviner la variable par lequel il faut instancier le terme
      - sinon il faut préciser la variable à instancier.

      Ici, Coq est assez malin pour trouver la variable tout seul.
   *)

  rewrite <- H.

  (** Le premier lemme est maintenant inutile. On peut le supprimer du contexte avec la tactique clear *)
  clear H.

  (** Maintenant il va falloir appliquer un certain nombre de fois l'associativité de plus. Cependant, le lemme peut s'appliquer un peu n'importe où. Comment décider où l'appliquer ? On peut préciser certains termes : *)
  rewrite <- (H0 _ n4 _).

  (** Le plus simple ici consiste tout de même à l'appliquer autant de fois que nécessaire. Cela peut se faire à l'aide de la tactique repeat. repeat est une autre tacticielle qui applique autant de fois que possible une tactique. *)
  repeat rewrite H0.

  (** Il est aussi possible d'utiliser des procédures de décision en Coq qui font le travail à notre place. On peut par exemple utiliser omega *)
  Undo. Undo.
  Require Import Omega.
  omega.
Defined.


(** Conclusion :
    - On a vu comment manipuler des hypothèses de la forme a = b avec rewrite ou subst
    - On a vu nos deux premières tacticielles :
         - now  qui permet de conclure un goal à l'aide d'une tactique
         - repeat qui permet de répeter une tactique jusqu'à ce qu'elle échoue
    - Souvent, on aura besoin des lemmes de la librairie standard. Pour trouver le nom du lemme à utiliser, on peut utiliser la commande Search.
    - On a vu une nouvelle tactique pose proof qui permet d'introduire un lemme dans le contexte.
    - On a pu noter que certains goals trivials peuvent être contraignants à prouver.
    - Pour pallier à ce souci, on peut utiliser des procédures de décision.
*)

(** ** 5. Les types inductifs *)

(** Objectif :
     - Présentation des types inductifs et du pattern matching
     - Introduction de la tactique destruct, induction et inversion
*)

(** Il y a plusieurs façons d'aborder les types inductifs. Pour les gens venant de la programmation fonctionnelle, il peut être intéressant de voir les types inductifs comme une généralisation des types algébriques. L'exemple canonique de type inductif ce sont les entiers naturels. En Ocaml, on pourrait écrire le type suivant :

type nat = O | S of nat

l'équivalent en Coq est le type inductif suivant : *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(**  Contrairement à OCaml, on peut appliquer les constructeurs partiellement : *)

Check S.

(** Les types inductifs de Coq viennent aussi avec un principe d'élimination. Pour les entiers naturels cela se traduit tout simplement par le principe d'induction que l'on connaît bien. *)

Check nat_ind.

(** Ce principe d'induction est décliné en trois versions en fonction de la sorte d'arrivée du prédicat. Dans notre cas, seul nat_ind et nat_rec nous intéressent. Le premier permet de faire une raisonnement inductif, tandis que le second permet de créer des fonctions récursivement. Cependant en général, Coq manipule ces fonctions de façon transparente et on ne manipulera pas ces termes directement. *)

(** Voici par exemple comment définir plus en Coq. Ici on introduit la commande Fixpoint qui permet d'écrire des fonctions _structurellement_ récursives en Coq. Si Coq ne trouve pas d'argument structurellement décroissant, la définition sera rejetée. *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => n
  | S n => S (plus n m)
  end.

(** On peut matcher sur les types inductifs comme on a l'habitude de le faire en OCaml. En Coq, une des façons de calculer provient directement du pattern-matching : *)

Eval compute in (plus (S (S O)) O).

Eval compute in (plus (S O) (S O)).

(** Quand on fait un match n with et que n est une valeur, alors Coq sait automatiquement dans quelle branche on est et donc réduire le terme de départ n. C'est ce qui explique la _bizarrerie_ que l'on a observée tout à l'heure avec n + 0 = n . n n'étant pas une valeur, Coq ne sait pas s'il doit passer dans la première branche ou bien dans la seconde. Donc n + 0 est déjà en _forme_normale_ . Cependant, il est possible de _prouver_ que n + 0 = n. *)

Lemma plus_n_0 : forall n, n + 0 = n.
Proof.
  intros n.

  (** Afin d'aider Coq, on voudrait distinguer 2 cas. Soit n = 0, soit n = S n'. Pour cela, on peut utiliser la tactique destruct *)

  destruct n.

  (** A noter que Coq génère deux goals, un pour chaque cas. Automatiquement Coq focus un goal. Il est possible d'en changer à l'aide de la commande Focus n. Ici, pour le cas où n = 0, c'est simple. *)

  reflexivity.

  (** Dans le cas inductif, on peut simplifier l'expression *)

  simpl.

  (** et là, on est à nouveau bloqué ! Pour s'en sortir, il va falloir faire une preuve par induction. *)
  Restart.

  (** une preuve par induction se fait avec la tactique induction *)

  intros n.
  induction n.

  (** on recommence... *)

  easy.
  simpl.

  (** Cette fois, on peut utiliser notre hypothèse d'induction pour réécrire notre but *)

  now rewrite IHn.
Qed.

(** induction est malin et trouve tout seul sur quelle propriété il faut appliquer le principe d'induction. En général ce sera toujours le cas, mais il peut y avoir des différences. C'est ce que l'on va voir sur l'exemple suivant. *)

(** On va chercher à prouver la commutativité de l'addition *)

Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
  easy.

  (** l'hypothèse d'induction que l'on a est : n + m = m + n . Autrement dit, m est fixé. Alors même si dans notre cas, cela ne pose pas de soucis, dans d'autres cas, cette hypothèse d'induction ne sera pas assez générale. Coq n'est pas assez malin pour généraliser tout ce qu'il peut généraliser. Donc faites attention quand vous souhaitez prouver des lemmes par induction à ce qu'il y a dans votre contexte. *)

  Restart.
  intro n.
  induction n.
  easy.

  (** vous voyez la différence ? Alors maintenant se pose le problème qu'il est possible que vous ayez introduit une variable dans le contexte et qu'à nouveau vous souhaitiez la réintroduire dans la goal pour que Coq puisse généraliser dessus. Dans ce cas, vous pouvez utiliser ou bien la tactique revert, ou bien la tactique generalize dependent. *)

  Restart.

  intros n m.
  revert m.
  Undo.
  generalize dependent m.
  induction n.
  easy.
  intro m.
  simpl.
  rewrite IHn.

  (** et là on est à nouveau bloqué ! *)
Abort.


(** Exercice : trouvez le lemme manquant et prouvez la commutativité de l'addition *)

(** Exercices : *)

Lemma plus_assoc : forall n m o, n + (m + o) = (n + m) + o.
Admitted.

Lemma times_comm : forall n m, n * m = m * n.
Admitted.

Lemma times_assoc : forall n m o, n * (m * o) = (n * m) * o.
Admitted.

Lemma plus_distr_r : forall n m o, (n + m) * o = (n * o) + (m * o).
Admitted.

(** Les listes existent aussi en Coq *)

Check list.

(** Les listes sont paramètrées par un type : *)

Check list nat.

Check list bool.

(** Comme pour Ocaml, la définition d'une liste se fait de façon inductive :*)

Print list.

(** Exercice : Définissez une fonction append qui concaténe deux listes *)

(** Exercice : Définissez une fonction length qui donne la longueur d'une liste *)

(** Exercice : Prouvez un lemme intéressant entre append et length *)

(** Avant de passer à la suite, il me reste à vous montrer une tactique qui peut s'avérer très utile en Coq : inversion. Supposons que vous souhaitez démontrer le lemme suivant : *)

Lemma trivial10 : forall x , x = 0 -> x + x = x.
Proof.
  intros x H.

  (** Ici on a besoin de faire un raisonnement par cas avec destruct *)

  destruct x.

  (** goal trivial *)

  easy.

  (** ici le goal est évidement faux, mais c'est parce que l'hypothèse H est elle même fausse. C'est à ce moment là que la tactique inversion entre en jeu. *)

  inversion H.

  (** et pouf magiquement le goal devient résolu. En effet, dès qu'une hypothèse dans le contexte est fausse, on peut prouver n'importe quoi y compris notre but. Cependant, au lieu d'utiliser destruct, on aurait pu directement utiliser inversion. La tactique aurait alors seulement générée un sous-but : *)
  Restart.

  intros x H.
  inversion H.
  easy.
Qed.

(** de façon générale, inversion est une bonne tactique pour détruire un type inductif dans un contexte. Contrairement à destruct, il arrive à deviner les cas possibles des cas impossibles *)


(** Conclusion :
    - On a vu comment déclarer des types inductifs simples.
    - On a vu qu'il est possible de matcher sur des types inductifs
    - Coq génère pour nous automatiquement des lemmes d'inductions sur ces types inductifs ce qui nous permet de créer des fonctions récursives et de faire des preuves par induction.
    - Il faut faire attention à l'utilisation de la tactique induction de sorte à récupérer la bonne hypothèse d'induction
    - inversion est une bonne tactique pour détruire des hypothèses sous-forme inductive dans un contexte
*)

(** ** 5. La logique de Coq *)

(** Objectifs :
     - Voir comment la logique de Coq est définie
     - introduction aux tactiques unfold et split
 *)
(** On a vu deux connecteurs logiques en Coq que sont l'implication et forall (ce sont des connecteurs primitifs de Coq). Les autres connecteurs logiques sont définis par des types inductifs. C'est ce que l'on va voir tout de suite. *)

Locate "/\".

Check and.

Print and.

(** conj est le seul constructeur de and. Maintenant, comment on voudrait pouvoir éliminer un and en projettant. Cela revient par exemple à prouver le lemme suivant : *)

Lemma proj1 : forall A B : Prop, A /\ B -> A.
Proof.
  intros A B H.

  (** Pour détruire un and dans une hypothèse, on peut utiliser destruct *)

  destruct H as [proofA proofB].
  easy.
Qed.

(** On peut aussi prouver le lemme suivant : *)

Lemma conj_and : forall (A B : Prop), A -> B -> A /\ B.
Proof.
  (** Quand on a un type inductif dans un goal, il est possible de le détruire. Ou bien en utilisant la tactique apply que l'on a déjà vue et en spécifiant le nom du constructeur : *)
  apply conj.

  (** Ici le but est trivial et Coq a déjà tout résolu. Quand seulement un constructeur peut s'appliquer, on peut aussi utiliser la tactique construcor : *)
  Undo.
  constructor.

  (** Enfin, vu que and et est tellement courant, on a crée une tactique juste pour lui : split *)

  Undo.
  split.
  easy.
  easy.
Qed.

(** Exercice : Définissez un type inductif pour le or. Prouvez un lemme d'élimination dessus. *)

(** Exercice : Définissez un type inductif pour le "il existe". *)

(** Cependant, la définition de ces connecteurs n'est pas unique. Par exemple : *)

Definition my_and (A B : Prop) := forall z:Prop, (A -> B -> z) -> z.

(** Exercice : il est possible de prouver les règles usuelles du et sur ce nouveau constructeur : *)

(** A noter que la tactique unfold permet de dérouler une définition *)

Lemma cons_my_and : forall (A B : Prop), A -> B -> my_and A B.
Proof.
  intros A B HA HB.
  unfold my_and.
Admitted.

Lemma my_and_proj1 : forall (A B : Prop), my_and A B -> A.
Proof.
  intros A B H.
  unfold my_and in H.
Admitted.

(** Exercice : Sans utiliser les types inductifs et seulement à l'aide du pour tout et de l'implication, créez une nouvelle définition my_or avec le comportement souhaité *)

(** Exercice : Dans le même esprit faites pareil avec la négation *)

(** Conclusion :
     - On a vu une définition possible des connecteurs logiques dans Coq, c'est celle qui est utilisée dans quasiment tous les développements
*)

(** Ouch ! On arrive enfin au bout de cette introduction, et je l'espère vous devriez avoir les bases pour commencer. On mettra en pratique ce qu'on a vu lors de la seconde session afin de prouver un algorithme de tri en Coq *)
