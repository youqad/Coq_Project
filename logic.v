Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.

Definition tiers_excl := forall (p: Prop), p \/ ~p.

Definition double_neg := forall (p: Prop), ~~p -> p.

Definition implic_classique := forall (p q : Prop), (p -> q) <-> ~p \/ q.


Theorem pierce_eq_tiers_ex : pierce <-> tiers_excl.
Proof.
  unfold pierce, tiers_excl.
  split.
  intros.
  apply H with (q:= False).
  intro.
  right.
  intro.
  apply H0.
  now left.
  intros.
  destruct (H p).
  assumption.
  apply H0.
  intro.
  contradiction.
Qed.

Theorem double_neg_eq_tiers_ex : double_neg <-> tiers_excl.
Proof.
  unfold double_neg, tiers_excl.
  split.
  intros.
  apply H.
  unfold not; intros.
  assert (~ p /\ ~~p).
  split.
  unfold not; intro.
    assert (p \/ ~p).
    now left.
    now apply H0 in H2.
  unfold not; intros.
    assert (p \/ ~p).
    now right.
    now apply H0 in H2.
  destruct H1.
  contradiction.

  intros.
  destruct (H p).
  assumption.
  contradiction.  
Qed.

Print double_neg_eq_tiers_ex.

Theorem implic_classique_eq_tiers_ex : implic_classique <-> tiers_excl.
Proof.
  unfold implic_classique, tiers_excl.
  split.
  intros.
  cut (~p \/ p).
  intro.
  destruct H0.
  now right.
  now left.
  now apply -> (H p p).

  intros.
  split.
  intro.
  destruct (H p).
  apply H0 in H1; now right.
  now left.
  intros.
  destruct H0.
  contradiction.
  assumption.
Qed.

