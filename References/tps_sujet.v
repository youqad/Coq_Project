(** *** Projet Coq 2014 - L3 S1 - Lucca Hirschi *)


(** Vous pouvez lire ce document dans sa version HTML mais l'id�al est de le compiler
au fur et � mesure pour lire les messages renvoy�s par Coq.
Vous avez besoin de Coq et d'un front-end (par exemple
CoqIDE par d�faut dans Coq ou Proof General pour l'interface avec Emacs).
Ce TP vous expliquera les notions essentielles de l'outil Coq. Il contient peu de questions
mais beaucoup d'explications. Assurez-vous donc de bien comprendre au fur et � mesure.
 *)
(** Lien vers la page du projet:
<<http://www.lsv.ens-cachan.fr/~hirschi/enseignements/progLogique/
>>
 *)

(************************)
(** * I : Introduction **)
(************************)

(** ** 1. G�n�ralit�s **)
(***********************)
(** Une des contributions de l'informatique � la logique sont les outils construisant
des preuves. Il existe deux cat�gories principales de ces outils:
 - les prouveurs automatiques tels que les SAT ou SMT solveurs ainsi que les model checkers, etc. 
   Vous en avez donc d�ja utilis� un lors du premier mini projet;
 - les assisants de preuves tels que Coq, Abella, PVS ou Agda, etc. Ce sont des outils interactifs
   construisant des preuves en demandent une intervention humaine mais qui automatisent certaines t�ches.

Dans ce projet on utilisera Coq (dans la seconde cat�gorie). En quelques mots, Coq est compos�:
- d'un "proof-checker" qui v�rifie que la preuve construite est bien une suite de r�gles logiques correctement utilis�es. C'est le (petit) noyau dans lequel il faut avoir confiance,
- d'un langage fonctionnel permettant de programmer et de formaliser des th�ories, calculs, etc.,
- et d'un langage de "tactiques" permettant d'automatiser certaines �tapes de preuves.
Le noyau de Coq repose sur de solides fondations: le calcul des constructions.
 *)

(** ** 2. D�marrer Coq **)
(************************)
(** Je vous conseille d'utiliser l'une des deux solutions suivantes:
 - l'IDE fourni avec COQ. Vous le lancez en tapant 'coqide' dans un terminal ou
 - le mode Emacs Proof General que vous pouvez trouver ici: 'http://proofgeneral.inf.ed.ac.uk/'.

Mais allez au plus simple pour pouvoir continuer � lire le sujet (dans Coq).
 *)

(** ** 3. Les types de Coq **)
(****************************)
(** Dans le langage de Coq (aka Gallina) vous pouvez �crire des formules, v�rifier
qu'elles sont correctement form�es et les prouver.*)
(** En Coq, tous les objets sont des termes du langage et ont donc un type que vous
    pouvez afficher avec la commande [Check [terme].] (toute commande Coq doit se
    terminer par un ".").*)
Check 3.
Check nat.
Check Set.
Check Type.
(** La notation [A:B] indique que le terme [A] a le type [B].
    On verra que de fa�on �quivalente, �a signifie �galement que [A] est une preuve
    de [B].*)
Check 1=2.
Check True.
Check (forall x:nat, x=0 \/ x>0).
Check Prop.
(** Bien-s�r, certains termes sont mal form�s comme [1+True] par exemple (essayez de compiler puis
commentez la ligne suivante): *)
 Check (1 + True).

(** Une bonne fa�on de s'y retrouver dans tous ces types est d'avoir en t�te que:
     - les termes de type [Prop] correspondent aux propositions logiques (ex. [1=2] ou [True]),
     - les termes de type [Set] sont des types de donn�es (ex. nat),
     - les termes de type [T] o� [T] est un type de donn�e (i.e., [T:Set]) sont des donn�es (ex. 1),
     - et.... [Type] est tout en haut (on a [Prop:Type] et [Set:Type]).
Avec un sch�ma �a donne (une arr�te signifie 'est de type'):
<<
                 Type
               /      \
            Set       Prop
           /  |      /    \
        nat  bool  True  ((1=0) \/ False)
       / |   /  \
      1  0  true false
>> *)
(** Dans la suite, on va rapidement voir la syntaxe de ce langage, � savoir comment �crire
des fonctions et des propositions et comment les prouver. On commence dans la section
suivante (II) avec les d�finitions de fonctions et de donn�es (on restera dans le monde [Set]).
Puis dans la section III sur les preuves, on plongera dans le monde [Prop].*)      



(******************************)
(** * II : Programmer en Coq **)
(******************************)

(** ** 1. Fonctions, calcul, bool *)
(** La commande [Require Import [module]] permet de charger les d�finitions, lemmes,
th�or�mes et leurs preuves d'un module. *)
Require Import Bool.
(** Je peux maintenant chercher toutes les d�finitons du module. *)
Search bool.
(** Je peux afficher la d�finition d'un terme avec [Print].*)
Print bool.
(** [bool] (qui est lui m�me de type [Set]) est un type de donn�e contenant deux �l�ments [true] et [false].
      On dit aussi que les habitants de [bool] sont [true] et [false].
      Quelle est la diff�rence avec [True:Prop]? *) 
Print ifb.
(** On peut donc �crire une fonction avec le mot cl� [fun] jouant le r�le d'un lambda: *)
Check (fun (b:bool) (n:nat) => if b then n else 0).
(** On note la distinction entre la fl�che [=>] des fonctions et celle des types: [->].
Si on veut d�finir un terme ou une fonction (pour l'utiliser par la suite), on utilise
le mot cl� [Definition]. L'exemple suivant comprend pas mal de points de syntaxe:*) 
Definition ifb2 (b : bool) (n:nat) := 
  let ntrue := n-1 in
  let nfalse := n in
  match b with
    | true => ntrue
    | false => nfalse
  end.
(** On peut aussi �crire: *)
Definition f := fun b:bool => b.
(** qui est �quivalent �: *)
Definition f2 (b:bool) := b.  
Print f.
Print f2.
(** On essaye d'appeler notre fonction: *)
Check (ifb2 true 1).
(** Et oui, Coq ne r�duit pas le terme qu'on lui donne, il v�rifie juste son type.
    Si on veut r�duire le terme, alors il faut invoquer [Eval compute in [terme]]
    et Coq va effectuer le calcul (purement symbolique!).*)
Eval compute in (ifb2 true 1).
(** En Coq, toute fonction est TOTALE. C'est-�-dire que les fonctions
    terminent TOUJOURS et renvoient un r�sultat du bon type. Il n'y a pas d'exceptions,
    d'erreurs � runtime ou d'Obj.magic.*)

(** **** Question 1:*)(** Ecrivez une fonction qui renvoie le XOR de trois bool�ens et testez-la. *)


(** ** 2. D�finitions inductives, points fixes et nat **)
(*******************************************************)
Print nat.
(** Les entiers sont repr�sent�s comme des entiers de Peano: c'est l'axiomatisation
    de Peano. Si vous voulez invoquer des propri�t�s sur les entiers qui ne sont pas des lemmes d�j�
    �crits (dans le module [Arith] par exemple) alors il faut les prouver dans Coq.*)
(** On note le mot cl� [Inductive] qui permet de d�finir:
      - un type de donn�es lui-m�me de type [Set] (ici c'est [nat]),
      - ainsi que les habitants de ce type (les termes qui ont ce type). Ici il n'y a que le
        terme 0 qui est un entier et le terme "S" (successeur) qui a le type [nat -> nat].
      C'est l'�quivalent d'une d�finition inductive par fermeture de r�gles (ou fonctions constructeurs)
      vue en logique. Dans le cas de [nat], on d�finit un ensemble inductif [nat] de termes par fermeture
      des fonctions constucteurs suivantes:
<<
                                      n : nat
     ----------------- [0]       --------------- [Succ]
          0 : nat                  S(n) : nat
        
>>
 *)
Search nat.
Print pred.
(** Ok, rien de nouveau. Maintenant, comment �crire [plus] ? Pensez-y avant d'avancer. *)
Print plus.
(** [fix] est un raccourci pour le mot cl� [Fixpoint] qui permet de d�finir des fonctions
r�cursives (un peu comme le "let rec" d'Ocaml).*)
Fixpoint mon_mult (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + mon_mult p m
  end.
(** Notez bien le message renvoy� par Coq apr�s la d�finition de fonction:
[mon_mult is recursively defined (decreasing on 1st argument)]. Coq d�tecte que
l'induction est bien fond�e. C'est de cette fa�on qu'il s'assure que toutes les fonctions
terminent. Le crit�re (syntaxique) de Coq est le suivant: un argument au moins DOIT �tre structurellement
plus petit au moment de l'appel r�cursif qu'� l'entr�e de la fonction. Regardez-les deux
exemples suivants.*)
Fixpoint fail1 (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + fail1 (S p) m
  (* et oui �a boucle ici *)
  end.
Fixpoint fail2 (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + fail2 (p + 0) m
  (** et oui c'est plus petit mais pas structurellement plus petit *)
  end.

(** **** Question 2:*)(** Ecrivez une fonction qui prend un entier et qui renvoie [true]
s'il est pair et [false] sinon. Ex�cutez cette fonction sur plusieurs exemples.  *)
(** **** Question 3:*)(** Ecrivez un type de donn�es [arbre] contenant une repr�sentation
de tous les arbres binaires �tiquet�s par des entiers.  *)
(** **** Question 4:*)(** Ecrivez une fonction qui renvoie la somme de toutes les �tiquettes
des noeuds d'un arbre. Testez.  *)
(** **** Question 5:*)(** Ecrivez une fonction qui prend deux entiers et qui renvoie
[true] si le premier est plus petit que le second et [false] sinon. Testez.  *)
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrivez une fonction qui calcule le pgcd de deux entiers. Testez.  *)


(** ** 3. Types polymorphes, listes et types d�pendants **)
(*********************************************************)
Require Import List.
Check list. Print list.
(** Le type [list] est une fonction qui prend un type [A] et renvoie un type (le type des
listes de type [A]).*)
Check (list nat).
Check 1 :: 2 :: 3 :: nil.
(** Mais qu'est-ce que c'est que "::" ? (tout est un terme en Coq).*)
Locate "::".
(** [Locate] nous informe que "[::]" est juste un mot cl� pour le terme [cons] (en notation infix).*)
(** Petit coup d'oeil rapide aux fonctions de [list].*)
Search list.  Check map. Print map.
Eval compute in map S (1::2::3::4::nil).
Eval compute in map (fun x => x +2) (1::2::3::4::nil).
Locate "++". Print app.
(** Tr�s bien mais il n'existe pas de fonction pour acc�der au n-ieme �l�ment
    d'une liste, pourquoi? *)


(** Jusqu'ici on a vu:
   - des termes d�pendant de termes (par exemple [S : nat -> nat]);
   - des types d�pendant de types (par exemple [list : Type -> Type]).
   Il existe aussi des types d�pendant de termes (aka types d�pendants).
   Voici un exemple de type d�pendant: un tableau de taille donn�e:*)
Inductive array (n : nat) : Type :=
  tab : forall l : list nat, length l = n -> array n.
(** [array] est de type [nat -> Type]. Par exemple, [array 10] est le type des tableaux de
    taille 10. *)
Check array.
Check (array 10 : Type).
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrire une fonction qui r�alise le fold_left polymorphique d'OCaml sur les listes.  *)
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrire une fonction de tri.  *)

(** ** 4. R�sum� **)
(******************)
(** Voici quelques lignes de Coq que vous devez comprendre (ainsi que les messages renvoy�s Coq).*)
Check true. Check bool. Check Set.
Print bool.
Fixpoint mon_exp (n m : nat) : nat :=
  match m with
    | 0 => 1
    | S m' => n * mon_exp n m'
  end.
Eval compute in (mon_exp 2 5).
Inductive formula : Type :=
  MonTrue : formula
| MonFalse : formula
| MonEt : formula -> formula -> formula
| MonOu : formula -> formula -> formula
| MonNon : formula -> formula.
Fixpoint eval (F : formula) : bool :=
  match F with
    | MonTrue => true
    | MonFalse => false
    | MonEt F1 F2 => if eval F1 then eval F2 else false
    | MonOu F1 F2 => if eval F1 then true else eval F2  
    | MonNon F' => negb (eval F')
  end.
Eval compute in (eval (MonOu (MonEt MonTrue MonFalse) (MonTrue))).



(****************************)
(** * III : Prouver en Coq **)
(****************************)
(** Dans la premi�re partie, on va d�couvrir ce qu'est une preuve en Coq. Ca risque
d'�tre un peu cosmique. Pour bien comprendre, il vaut mieux avoir entendu parler de la 
correspondence de Curry-Howard (cf. les r�f�rences donn�es sur ma page et le cours de lambda-calcul).
Mais pas de panique, dans la section suivante on va voir comment s'aider des tactiques les plus
importantes. Dans la derni�re section on verra l'induction.*)

(** ** 1. Une preuve en Coq **)
(*****************************)

(** Le but ici est de comprendre l'objet preuve de Coq.
On va prouver quelques lemmes compl�tement triviaux et �a vous para�tra
compliqu� mais le but est de comprendre ce qu'il se passe quand plus tard
vous prouverez des th�or�mes plus compliqu�s en utilisant de grosses tactiques.*)

  (** En fait on a d�j� �crit des preuves: [f:A] est une fonction de type A mais en Coq
on peut aussi appeler �a une preuve de la formule logique A : c'est la correspondence de Curry-Howard.
En r�sum�, une preuve Coq de la formule [A] c'est un terme de type [A]. *)
Check True.
(** [True] est un terme de type [Prop] c'est donc aussi une formule.
      A ne pas confondre avec le bool�en [true]. *)
(** On va prouver notre premier lemme: *)
Lemma tauto1 : True.
  (** On veut prouver [True], �a va �tre facile. En d�duction naturelle, il existe la r�gle
        Intro Top, en Coq on peut regarder ce que siginifie [True] et [False]:*)
  Print True. Print False.
  (** [True] est la formule qui n'a qu'un habitant [I] (traduction: le seul terme de type [True]
        est [I]). Prouver [True] revient � donner [I] qui a le bon type [I:True]. Bien s�r, [False]
        n'a pas d'habitant: on ne peut pas le prouver.*)
  apply I.
  (** La preuve est compl�te comme nous l'indique Coq.*)
Qed.
(** [Qed] demande � Coq de clore la preuve (une fois que tous les buts ont �t� prouv�s). Coq construit alors
le terme correspondant et lui donne le nom du lemme.*)
Print tauto1.
(** R�sum� de cette magnifique preuve:
        tauto1 est une preuve de True (= tauto1 est la fonction I de type True).
        On a prouv� True car on a construit un terme habitant dans ce type. *)

Lemma tauto2 (A B : Prop): A -> B -> A /\ B.
  (**
Voici quelques r�gles g�n�rales sur la construction de preuves en Coq:
 - Coq nous indique le nombres d'objectifs (cad. de preuves � construire) avant de pouvoir clore la preuve (ici un objectif sur un total d'un),
 - Pour chaque objectif, on visualise le but (sous la ligne continue) et les hypoth�ses
   que l'on a � disposition. En d�duction naturelle, on a [Gamma |- P] alors qu'en Coq, on a:
<<
            Gamma
            _______ (1/1)
            P
>>
 - La construction de la preuve est dirig�e par le but (ce qu'il faut montrer) un peu comme en d�duction naturelle. On ne construit donc pas la preuve en partant des axiomes. Toutefois, on verra que l'on peut manipuler les axiomes plus facilement qu'en d�duction natirelle,
 - On constuit la preuve en donnant � Coq une fonction � appliquer au but (qui va le remplacer par les sous-buts correspondants aux arguments de la fonction). On utilise le mot cl� [apply [fonction]],
 - Comme ce n'est pas tr�s pratique (on a vu �a avec [True]), on peut utiliser des tactiques pour s'aider. Il existe de nombreuses tactiques.
   Certaines vont essayer d'appliquer plusieurs fonctions selon la t�te du s�quent � prouver et permettent donc de gagner beaucoup de 
   temps/lignes. On en verra une petite liste dans la section suivante. Retenez bien qu'une tactique ne fait g�n�ralement pas partie de la preuve.
   Elle permet de chercher un terme � appliquer en fonction de la t�te du but et des hyptoh�ses.*)
  (** Ici, on va utiliser la tactique [intro]. Elle correspond � l'introduction de la fl�che en d�duction naturelle:
<<
         Gamma, P  |-  Q
         -----------------
         Gamma  |-  P -> Q
>>
   *)
  intro. intro. 
  (** Ou plus simplement [intros]. C'est une bonne habitude de nommer les hyptoh�ses
que l'on charge, ici j'aurais fait [intros HA HB] par ex. On doit d�sormais prouver une conjonction [/\].
On peut regarder ce que �a signifie. *)
  Locate "/\". Check and. Print and.
  (** [and] a le type [Prop] (c'est donc une formule) qui contient un seul habitant [conj] de type [A -> B -> and A B]. C'est comme cela qu'est encod�e la conjonction en Coq. Et donc, pour construire
  un terme de type [and A B] il faut construire des termes de type [A] et [B] et appliquer
cette fonction. *)
  Check conj. Print conj.
  apply conj.
  (** Cette fonction prenait deux arguments: il faut donc construire les termes (= preuves)
pour ces deux arguments, d'o� les deux sous-buts que Coq nous demande de prouver. *)
  (** On a le but en hypoth�se. Il suffit donc d'appliquer la fonction H (de type A). *)
  apply H.
(** On a prouv� le premier sous-but. Il reste le second sous-but. *)
  apply H0.
Qed.

(** On peut afficher le terme que l'on a construit (vous serez d��u ;) ): *)
Print tauto2.
(** Le terme que l'on a construit est simplement [conj]. On aurait pu pour prouver ce petit lemme
    directement en disant � Coq: "voici un terme habitant dans le type � prouver". On peut le faire
    en utilisant [exact]: *)
Lemma tauto2bis: forall A B : Prop, A -> B -> A/\B.
  exact conj.
Qed.
(** Tout �a fait sens grace � la correspondance de Curry-Howard:
<< Le s�quent [Gamma |- A] est prouvable en d�duction naturelle intuitionniste
si et seulement s'il existe un lambda-terme [t] tel que [Gamma |- t : A]
(quitte � r�indexer Gamma).
>>
O� [Gamma |- t : A] d�note que [t] a le type [A] dans le contexte de typage [Gamma].
*)

(** On va maintenant prouver un lemme un poil plus compliqu�. Mais cette
      fois, je vais utiliser des tactiques et on regardera le terme produit. *)
Lemma tauto3 : forall A B : Prop, A/\B -> B/\A.
  intros A B H.
  (** On NOMME ces hypoth�ses *)
  destruct H.
  split.
  apply H0.
  apply H.
Qed. Print tauto3.
(** Ouf, comment on a fait ce pattern-matching? *)
(** H est de type [and] qui ne contient que le constructeur conj, on peut donc
r�aliser un pattern-macthing sur le terme H. C'est ce que fait [destruct]: il n'y
a qu'un pattern possible (car il n'y a qu'un seul habitant dans [and A B]) et on r�cup�re
les deux hypoth�ses [A] et [B] venant des arguments de conj.
On remarque qu'ici, destruct fait la m�me chose que la r�gle de la conjonction gauche du calcul des s�quents:
<<
         Gamma, A, B  |-  Q
         ------------------
         Gamma, A/\B  |-  Q
>>*)

(** Ensuite [split] va appliquer la fonction constructeur associ�e au but (ici c'est la fonction conj) et
donc g�n�rer les deux sous-buts correspondant � ses arguments.
[split] correspond donc � la r�gle de l'introduction de la conjonction en d�duction naturelle:
<<
         Gamma |-  P    Gamma |-  Q
         --------------------------
         Gamma |-  P/\Q
>>
Et on conclut avec l'application des hypoth�ses.*)

(** On peut aussi r�utiliser un lemme d�j� prouv� (�a revient � appliquer le terme construit
lors de la preuve de ce lemme).*)
Lemma tauto3' : forall A B : Prop, A/\B -> B/\A.
  intros A B AB.
  (** On NOMME ces hypoth�ses *)
  destruct AB.
  apply tauto2.
  apply H0. apply H.
Qed.


(** ** 2. Tactiques principales **)
(*********************************)
(** On peut s'amuser � construire le terme qui a exactement le bon type.
Mais Coq nous permet de construire la preuve/fonction de fa�on interactive. Et c'est de cette fa�on
qu'on �crira des preuves plus tard. On va se servir du "Coq cheat sheet" pour prouver quelques propri�t�s
de logique propositionnelle.
Prenez la page 2 de ce document.
 *)
Lemma or_comm : forall A B, A\/B -> B\/A.
Proof.
  intros A B AoB.
  destruct AoB.
  Print or.
  (** Et oui, si on fait [Print or] alors on se rend compte que le type [or] contient
   deux habitants (les deux projections): [or_introl : A -> A \/ B] et [or_intror : B -> A \/ B].
   Donc [destruct] va faire le pattern-matching de ces deux cas ce qui aura pour effet
   de cr�er deux sous-buts suivant le pattern choisi. C'est exactement la r�gle de la disjonction gauche
   (\/ left) du calcul des s�quents. *)
  right. auto.
  (** On a simplement choisi quelle c�t� de la disjonction on voulait prouver (comme le permet les deux r�gles
de l'introduction de la disjonction (\/I1 et \/I2) de la d�duction naturelle par exemple) et on a invoqu�
une hypoth�se. [auto] est une tactique qui va chercher dans les hypoth�ses s'il n'y a pas directement le but. *)
  left. auto.
Qed.
Print or_comm.

(** On va d�finir le pr�dicat "si et seulement si". On appelle "pr�dicat" un objet qui renvoie
 un [Prop] (une formule). *)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
(** On va maintenant prouver quelques lemmes sur ce pr�dicat. *)
Lemma iff_implies : forall P Q, iff P Q -> (P -> Q).
Proof.
  intros P Q H.
  (** Quand une hypoth�se (ou la conclusion) contient une formule dont vous avez oubli� la d�finition, vous pouvez l'unfolder de cette fa�on:  *)
  unfold iff in H.
  destruct H as [HPQ HQP].
  (** Le [as [nom1 nom2]] me permet de nommer les hypoth�ses g�n�r�es par le [destruct]: c'est une
   bonne habitude de tout nommer. *)
  auto.
Qed.

Lemma iff_sym : forall P Q, (iff P Q) -> (iff Q P).
Proof.
  intros P Q H.
  destruct H as [HPQ HQP].
  split; auto. 
(** Dans la ligne pr�c�dente j'utilise le point virgule entre split et auto pour demander � Coq
 d'appliquer automatiquement [auto] � tous les sous-buts g�n�r�s par [split]. Le point virgule est tr�s
utile pour automatiser certaines t�ches redondantes.*)
Qed.

(** **** Question 6:*)(** Prouvez les lemmes suivants:*) 


(** On d�finit maintenant le pr�dicat sur les entiers "est un entier pair". Pour constuire
un pr�dicat en Coq, il faut:
  - lui donner un nom et un type (ici [even : nat -> Prop],
  - d�finir les r�gles d'inf�rences (et leur donner des noms) qui permettent de d�finir ce pr�dicat.
    Dans notre cas, il y en a deux que l'on nommera even0 et evenS. La premi�re dit simplement que 0 est
    pair (sans autre hypoth�se). La seconde dit que sous l'hypoth�se que [x] est pair alors [x+2] est pair.*)
Inductive evenP : nat -> Prop :=
  even0 : evenP 0
| evenS : forall x:nat, evenP x -> evenP (S (S x)).

(** Cette d�finition est la traduction en Coq du pr�dicat [evenP] d�fini avec les r�gles d'inf�rences suivantes:
<<
                         evenP x
--------- even0    et    ------------ evenS
evenP 0                  evenP (x+2)
>>
 *)
(** Attention: en �crivant ce type de donn�es, on n'a pas prouv� que tout entier �tait pair. On a construit
un terme qui prend un entier et qui renvoie la formule qui dit "l'entier est pair".
Le lemme (faux) qui dit que tout entier est pair est [forall n, evenP n].*)
(** **** Question 7:**) (** Prouvez maintenant que deux est pair: *)
(** **** Question 8:**) (** D�finissez le pr�dicat "plus petit que" de type [nat -> nat -> Prop].
Quelle est la diff�rence avec ce que vous avez �crit pour la question 5 ?
Prouvez que 3 et plus petit que 6.*)
(** **** Question 9:**) (** D�finissez le pr�dicat "estTrie" de type [list nat -> Prop].
Prouvez que [3 :: 6 :: nil] estTrie. *)

(** ** 3. Preuves inductives et recherche de lemmes **)
(*****************************************************)
(** Si on veut montrer, par exemple, que [n+1] n'est pas pair si [n] est pair alors on va avoir
besoin de raisonner par induction (vous en �tes convaincu?).
Ca tombe bien parce que quand on d�finit un objet inductif,
Coq nous fournit automatiquement un axiome d'induction structurelle. Pour les entiers c'est: *)
Check nat_ind.
(** C'est bien le sch�ma par induction habituel: on peut donc appliquer ce terme quand on veut
   faire une induction ou alors, de fa�on �quivalente, appeler la tactique [induction].
On va s'en servir dans la preuve suivante. *)
Require Import Arith.
Lemma sum_even : forall n,  evenP n -> ~ evenP (S n).
Proof.
  intros n En.
  unfold not.
  intro ESn.
  (** On va faire une induction sur n: *)
  induction n.
  (** On doit traiter le cas n=0 (initialisation): *)
  (** Dans ce cas, on se rend compte que ESn n'est pas possible. On va utiliser
   la tactique [inversion] qui va traiter les diff�rents cas possibles de evenP
   en �liminant ceux qui sont impossibles. *)
  inversion ESn.
  (** Cas inductif: on commence par utiliser l'hypoth�se d'induction. *)
  apply IHn.
  (** On sait que n+2 est pair: on va donc inverser ESn et on aura que n est pair *)
  inversion ESn.
  auto.
  auto.
Qed.
(** [nat_ind] est en fait un lemme qui est automatiquement g�n�r� � partir de la d�finition
    inductive de [nat]. Et �a marche pour tous les pr�dicats inductifs. Par exemple: *)
Check evenP_ind.
(** On comprend qu'en fait ces lemmes sont des inductions strcuturelles (induction sur la d�rivation qui permet de d�river le pr�dicat. M�ditez l�-dessus... *)

(** Dans les preuves sur les entiers, on a souvent besoin d'utiliser des axiomes ou de petits
    lemmes triviaux pour r��crire des termes. Regardons cet exemple: *)
Lemma pasSiFacile : forall n, n*2 + 0 = 1 - 1 + n + n.
  intro n.
  (** On a besoin d'expliquer � Coq que le [+ 0] ne sert � rien.
     Pour cela,on va chercher l'axiome qui dit que [n+0=n] (c'est vrai car 0 est le neutre de +, �a fait
parti de l'axiomatisation des entiers dans Coq). On a diff�rentes fa�ons de chercher un lemme dans Coq:
     - [Search [objet]] cherche tous les lemmes prouvant une formule contenant [[objet]];
     - [SearchAbout [formule]] cherche tous les lemmes contenant [[formule]];
     - [SearchPattern [pattern]] cherche tous les lemmes prouvant une formule contenant [[pattern]];
     - [SearchRewrite [pattern]] cherche tous les lemmes dont la conclusion est une �galit� contenant [[pattern]].*)
  Search le.
  SearchAbout le.
  SearchRewrite (_ + 0).
  (** On va donc utiliser le lemme [plus_n_O] pour r��crire notre but. On utilise la tactique 
[rewrite] (avec une fl�che [<-] si on veut r��crire dans le sens contraire). *)
  rewrite <- plus_n_O.
  (** (On peut aussi utiliser plus_0_r) *)
  SearchRewrite (_ - _).
  rewrite -> (minus_diag 1).
  (** **** Question 10:*)(** Terminez la preuve (sans autre tactique que [rewrite] et [reflexivity]). *) 
Qed.
(**  *)
(** **** Question 11:*)(** Prouvez les lemmes suivants (r�fl�chissez � la preuve sur papier au pr�alable et sachez que vous pouvez faire des inductions sur les pr�dicats inductifs): *) 
Lemma even_double : forall n, evenP n -> exists (m m2 : nat), n = 2*m.
Qed.

Require Import Omega.
(** La tactique [omega] r�sout tous les probl�mes de syst�mes d'in�quations et d'�quations lin�aires. *)
Lemma double_even : forall n, evenP (2*n).
Qed.

Lemma sum_pair : forall n m, evenP n -> evenP m -> evenP (n+m).
Qed.

(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Prouvez que la fonction de tri que vous avez �crite est correcte
en utilisant le pr�dicat "estTrie" de la question 9. C'est tout pour la correction? *)
