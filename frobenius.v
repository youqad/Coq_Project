Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.

Definition tiers_exclus := forall (p: Prop), p \/ ~p.

Theorem pierce_equiv_tiers_ex : pierce <-> tiers_exclus.
Proof.
  unfold pierce, tiers_exclus.
  split.
  intros H p.
  apply H with (q:= False).
  intro f.
  right.
  intro xp.
  apply f.
  left.
  exact xp.
  intros H p q H0.
  destruct (H p).
  assumption.
  apply H0.
  intro xp.
  apply H1 in xp.
  destruct xp.
  Qed.


Theorem frobenius (A : Set) (p : A -> Prop) (q: Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.
  intros [x [H1 H2]].
  split.
  assumption.
  exists x.
  assumption.
  intros [H1 [x H2]].
  exists x.
  split; assumption.
Qed.

Definition lem := forall p, p \/ ~p.

Definition dual_frobenius := forall (A : Set) (p : A -> Prop) (q: Prop), (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).



Theorem lem_dualfrobenius : lem <-> dual_frobenius.
Proof.
  unfold lem, dual_frobenius.
  split.
  intros.
  split.
  intros.
  destruct (H q).
  left.
  assumption.
  right.
  intro x.
  destruct (H0 x).
  apply H1 in H2.
  destruct H2.
  assumption.
  intros H0 x.
  destruct H0.
  left; assumption.
  right.
  apply H0 with (x := x).

  intros H p.
  destruct (H p (fun _ => False) p) as [H0 _].
  cut (p \/ (p -> False)). easy.
  apply H0.
  intros x; left; assumption.
Qed.

Parameters A B C : Set.

Definition curry (f : A * B -> C) := fun a => fun b => f(a, b).

Definition uncurry (f : A -> B -> C) := fun p => f (fst p) (snd p).


Theorem inverse : forall f a b, curry (uncurry f) a b = f a b.
Proof.
  intros f a b.
  unfold uncurry, curry.
  simpl; reflexivity.
Qed.


