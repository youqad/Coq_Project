(************************)
(** * V : Rajouter la logique classique en Coq  **)
(************************)

(** *** Projet Coq 2017 - Younesse Kaddar *)

(** ** 1. Modéliser les axiomes suivants :
    - La loi de Peirce
    - L’élimination de la double négation
    - Le tiers-exclu
    - La définition classique (au sens logique) de l’implication
    - Les lois de de Morgan
 **)
(***********************)





Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.

Definition tiers_excl := forall (p: Prop), p \/ ~p.

Definition double_neg := forall (p: Prop), ~~p -> p.

Definition implic_classique := forall (p q : Prop), (p -> q) <-> ~p \/ q.

Definition de_morgan1 := forall (p q : Prop), ~ (p \/ q) <-> (~ p) /\ (~ q).
Definition de_morgan2 := forall (p q : Prop), ~ (p /\ q) <-> (~ p) \/ (~ q).

(** ** 2. Montrer constructivement (sans nouvel axiome) l'équivalence entre tous ces axiomes.
 **)
(***********************)

(** *** On va montrer que les 4 premiers sont équivalents à notre préféré : le tiers exclus. *)

Theorem pierce_eq_tiers_ex : pierce <-> tiers_excl.
Proof.
  unfold pierce, tiers_excl.
  split.
  - (* => *)
    intros H p.
    apply H with (q:= False).
    intro H0.
    right.
    intro.
    apply H0.
    now left.
  - (* <= *)
    intros H p q H0.
    destruct (H p).
    assumption.
    apply H0.
    intros H2.
    contradiction.
Qed.

Theorem double_neg_eq_tiers_ex : double_neg <-> tiers_excl.
Proof.
  unfold double_neg, tiers_excl.
  split.
  - (* => *)
    intros H p.
    apply H.
    unfold not; intros.
    assert (~ p /\ ~~p).
    {
      split.
      + unfold not; intro.
        assert (p \/ ~p).
        { now left. }
        now apply H0 in H2.
      + unfold not; intros.
        assert (p \/ ~p).
        { now right. }
        now apply H0 in H2.
    }
    destruct H1.
    contradiction.
  - (* <= *)
    intros H p H0.
    destruct (H p).
    assumption.
    contradiction.  
Qed.


Theorem implic_classique_eq_tiers_ex : implic_classique <-> tiers_excl.
Proof.
  unfold implic_classique, tiers_excl.
  split.
  - (* => *)
    intros H p.
    cut (~p \/ p).
    {
      intro H0.
      destruct H0.
      + now right.
      + now left.
    }
    now apply -> (H p p).

  - (* <= *)
    intros H p q.
    split.
    + intro H0.
      destruct (H p).
      * apply H0 in H1; now right.
      * now left.
    + intros H0 H1.
      destruct H0.
      * contradiction.
      * assumption.
Qed.


(** *** Montrons que [de_morgan1], et que le sens indirect de [de_morgan2] sont des tautologies intuitionnistes. *)

Theorem de_morgan1_tauto : de_morgan1.
Proof.
  unfold de_morgan1.
  intros p q.
  split.
  - (* => *)
    intro H.
    split.
    + intro; apply H; now left.
    + intro; apply H; now right.
  - (* <= *)
    intro H.
    destruct H.
    intro.
    destruct H1.
    + now apply H in H1.
    + now apply H0 in H1.
Qed.



Theorem de_morgan2_tauto_indirect : forall (p q : Prop), (~ p) \/ (~ q) -> ~ (p /\ q).
Proof.
  intros p q H.
  destruct H.
  - intro; apply H; now destruct H0.
  - intro; apply H; now destruct H0.
Qed.

