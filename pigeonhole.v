(************************)
(** * VI : Le principe des tiroirs  **)
(************************)
(** *** Projet Coq 2017 - Younesse Kaddar *)


Require Import List.
Require Import PeanoNat.
Require Import Nat.


(** ** 1. Définir un prédicat simple [repeats] qui est vrai si et seulement si la liste [l1] se répète
 **)
(***********************)


Variable X : Type.

Inductive repeats : list X -> Prop :=
| base_repeats : forall x l, In x l -> repeats (x::l)
| rec_repeats : forall x l, repeats l -> repeats (x::l).

(** ** 2. Modéliser l’énoncé ci-dessus en Coq
 **)
(***********************)


Definition embedded (X:Type) (l1 l2 : list X) := (forall x, In x l1 -> In x l2).

Definition pigeonhole (l1 l2 : list _) := embedded X l1 l2 -> length l2 < length l1 -> repeats l1.

Definition tiers_excl := forall (p: Prop), p \/ ~p.

Axiom tiers_ex : tiers_excl.

(** ** 3. Prouver votre énoncé (vous pouvez utiliser un des axiomes classiques
présentés dans la partie V).
 **)
(***********************)



Lemma In_bisect : forall (x : X) l, In x l -> (exists l' l'', l = l' ++ (x::l'')).
Proof.
  intros x l H.
  induction l.
  - easy.
  -
    destruct (tiers_ex (x = a)).
    +
      exists nil, l.
      simpl; now rewrite H0.
    +
      destruct H.
      * symmetry in H; contradiction.
      * apply IHl in H.
        destruct H as [l' [l'' H1]].
        exists (a::l'), l''; simpl.
        now rewrite H1.
Qed.

Lemma In_incl : forall (x a : X) l, In x l -> In x (a::l).
Proof.
  intros; simpl; now right.
Qed.


Lemma In_neq : forall (x a : X) l' l'', x <> a -> In x  (l' ++ (a::l'')) -> In x  (l' ++ l'').
Proof.
  intros x a l' l'' H H0.
  induction l'.
  -
    simpl in H0.
    destruct H0.
    symmetry in H0.
    contradiction.
    now simpl.
  -
    destruct (tiers_ex (a0 = x)).
    +
      now left.
    +
      right.
      destruct H0.
      contradiction.
      now apply IHl' in H0. 
Qed.



Theorem classic_pigeonhole : forall l1 l2, pigeonhole l1 l2.
Proof.
  unfold pigeonhole; unfold embedded.
  intro l1.
  induction l1.
  - easy.
  - destruct (tiers_ex (In a l1)).
    + now constructor.
    + intros l2 H0 H1.
      cut (repeats l1).
      { now constructor. }
      assert (exists l2' l2'', l2 = l2' ++ (a::l2'')).
      {
        cut (In a l2).
        { apply In_bisect. }
        apply H0.
        now left.
      }
      destruct H2 as [l2' [l2'' H2]].
      apply IHl1 with (l2 := l2'++l2'').
      intros x H3.
      destruct (tiers_ex (x=a)).
      * rewrite H4 in H3; contradiction.
      * rewrite H2 in H0.
        assert (In x (a :: l1)).
        { now apply (In_incl x a) in H3. }
        apply H0 in H5.
        now apply (In_neq x a).
      * rewrite H2 in H1.
        simpl in H1.
        cut (length (l2' ++ a :: l2'') = S(length (l2' ++ l2''))).
        {
          intro H3.
          rewrite H3 in H1.
          now apply Lt.lt_n_Sm_le in H1.
        }
        (* il s'agissait d'un exercice du tuto introductif *)
        repeat rewrite app_length; now simpl.
Qed.

(** ** 3. Prouver votre énoncé du principe des tiroirs constructivement cette fois.
 **)
(***********************)

(** En suivant l'indication de l'énoncé, qui nous invite à exploiter la décidabilité de l'égalité sur les entiers, on est tenté de :
    - définir une fonction [natify] transformant une [list X] en la liste de ses indices
 *)

Fixpoint natify' (X:Type) (l2 : list X) (k : nat) : list nat :=
  match l2 with
  | nil => nil
  | h::t => k::(natify' X t (k+1))
  end.

Definition natify (X:Type) (l2 : list X) : list nat := natify' X l2 0.

(** - enchaîner avec la définition d'un prédicat [linked] formalisant le fait qu'une [list X] [l1] s'injecte dans une [list X] [l2] par le biais d'une [list nat] [l3'], laquelle s'injecte elle-même dans la [list nat] [l3 = natify l2] *)

Inductive linked : list X -> list X -> Prop :=
| base_link : forall l2, linked nil l2
| rec_link : forall l1 l2 x,
    embedded X (x::l1) l2
    -> (exists (l3' : list nat), embedded nat l3' (natify X l2)
    -> forall i, List.nth (List.nth i l3' 0) l2 x = List.nth i (x::l1) x)
    -> linked (x::l1) l2.

(** - Puis, prouver des lemmes tels que :
      -- [[
Lemma embedded_incl : forall l1 l2 x, embedded X (x::l1) l2 -> embedded X l1 l2 /\ In x l2.
Proof.
  unfold embedded.
  intros.
  split.
  intros.
  apply (In_incl x0 x) in H0.
  now apply H in H0.
  apply H.
 now constructor.
Qed.
]]

-- [embedded_implies_linked : forall l1 l2, embedded X l1 l2 -> linked l1 l]

 *)

(** Pour enfin déboucher sur le principe des tiroirs intuitionniste. *)


(** Mais je pense avoir trouvé plus simple, en restant dans les clous de l'énoncé. *)


(** En définissant un nouveau prédicat [repeats2], qui vérifie la caractérisation de la question 1 : *)

Inductive not_repeats : list X -> Prop :=
| base_not_repeats : not_repeats nil
| rec_not_repeats : forall x l, not_repeats l -> ~ In x l -> not_repeats (x::l).

Definition repeats2 l := ~ not_repeats l.

(** On peut démontrer, modulo le lemme intuitionniste suivant (moins fort que [In_bisect]) : *)

Lemma In_delete : forall (x:X) l2, In x l2 -> exists l2',
      (length l2 = S (length l2')) /\ (forall y, y <> x -> In y l2 -> In y l2').
Proof.
  induction l2.
  - intro H.
    inversion H.
  - intro H.
    destruct H.
    subst a.
    exists l2.
    split.
    + now simpl.
    + intros y H H0.
      destruct H0.
      * symmetry in H0; contradiction.
      * assumption.
    + apply IHl2 in H.
      destruct H as [l2' [H0 H]].
      exists (a::l2').
      split.
      * simpl.
        now rewrite <- H0.
      * intros y H1 H2.
        destruct H2.
        -- now left.
        -- right.
           now apply H.
Qed.

(** le principe des tiroirs intuitionniste : *)

Definition pigeonhole2 (l1 l2 : list _) := embedded X l1 l2 -> length l2 < length l1 -> repeats2 l1.

Theorem intuitionistic_pigeonhole : forall l1 l2, pigeonhole2 l1 l2.
Proof.
  unfold pigeonhole2; unfold embedded.
  intro l1.
  induction l1.
  - easy.
  - unfold repeats2.
    intros; intro.
    inversion H1.
    subst a.
    assert (H' := H).
    apply (In_delete x) in H'.
    destruct H' as [l2' [H2 H']].
    apply (IHl1 l2').
    + intros x0 H6.
      apply H'.
      intro.
      subst x0; now contradiction.
      apply (In_incl x0 x) in H6.
      now apply H in H6.
    + rewrite H2 in H0; simpl in H0.
      now apply Lt.lt_n_Sm_le.
    + assumption.
    + simpl; now left.
Qed.



