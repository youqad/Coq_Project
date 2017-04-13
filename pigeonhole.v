Require Import List.
Require Import PeanoNat.
Require Import Nat.


Variable X : Type.

Inductive repeats : list X -> Prop :=
| twice_repeats : forall x, repeats (x :: x :: nil)
| in_repeats : forall x l, repeats l \/ In x l -> repeats (x::l).

Definition pigeonhole (l1 l2 : list _) := (forall x, In x l1 -> In x l2) -> length l2 < length l1 -> repeats l1.

Definition tiers_excl := forall (p: Prop), p \/ ~p.

Axiom classic : tiers_excl.

Search "<=".

Lemma In_incl : forall (x a : X) l, In x l -> In x (a::l).
Proof.
  intros.
  simpl.
  now right.
Qed.

Lemma len_lemma : forall l1 l2 (a : X), (forall x, In x (a :: l1) -> In x l2) -> ~repeats l1 -> ~ In a l1 -> length l1 <= length l2.
Proof.
  pose proof classic as tiers_exlc.
  induction l1.
  intros.
  simpl.
  apply Nat.le_0_l.
  intros.
  assert (~ repeats l1 /\ ~In a l1).
  split.
  destruct (tiers_exlc (repeats l1)).
  cut (repeats (a :: l1)).
  intro; contradiction.
  constructor.
  now left.
  assumption.
  destruct (tiers_exlc (In a l1)).
  cut (In a0 (a :: l1)).
  intro; contradiction.
  apply In_incl.
  now left.
  assumption.
Admitted.


Theorem classic_pigeonhole : forall l1 l2, pigeonhole l1 l2.
Proof.
  pose proof Nat.nlt_0_r as nlt_0.
  pose proof classic as tiers_exlc.
  pose proof Lt.lt_n_Sm_le as lt_S.
  pose proof Nat.nlt_ge as nlt_ge.
  pose proof Nat.le_antisymm as le_antisymm.


  intros.
  unfold pigeonhole.
  intros.
  induction l1.
  simpl in H0.
  apply nlt_0 in H0; contradiction.
  intros.
  simpl in H0.
  destruct (tiers_exlc (length l2 < length l1)).
  destruct (tiers_exlc (forall x : X, In x l1 -> In x l2)).
  cut (repeats l1 \/ In a l1).
  now constructor.
  left.
  now apply (IHl1 H2 H1).
  assert (forall x : X, In x l1 -> In x l2).
  intros.
  apply (In_incl x a) in H3.
  now apply H in H3.
  contradiction.
  destruct (tiers_exlc (repeats l1)).
  cut (repeats l1 \/ In a l1).
  now constructor.
  now left.
  apply nlt_ge in H1.
  apply lt_S in H0.
  assert (length l1 = length l2) as len.
  apply le_antisymm.
  exact H1.
  exact H0.
  clear H0.
  clear H1.
  destruct (tiers_exlc (In a l1)).
  cut (repeats l1 \/ In a l1).
  now constructor.
  now right.


Qed.


  (* pose proof Lt.lt_n_Sm_le as lt_n_Sm_le. *)
  (* pose proof Lt.le_lt_or_eq as le_lt_or_eq. *)
  (* assert (forall n m : nat, n < S m -> n < m \/ n = m) as lt_S1. *)
  (* intros. *)
  (* apply le_lt_or_eq. *)
  (* now apply lt_n_Sm_le in H. *)
  (* clear lt_n_Sm_le. *)
  (* clear le_lt_or_eq. *)
