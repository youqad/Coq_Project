Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Coq.omega.Omega.


Variable X : Type.

Inductive repeats : list X -> Prop :=
| base_repeats : forall x l, In x l -> repeats (x::l)
| rec_repeats : forall x l, repeats l -> repeats (x::l).

Definition pigeonhole (l1 l2 : list _) := (forall x, In x l1 -> In x l2) -> length l2 < length l1 -> repeats l1.

Definition tiers_excl := forall (p: Prop), p \/ ~p.

Axiom classic : tiers_excl.

Search "<=".


Lemma In_bisect : forall (x : X) l, In x l -> (exists l' l'', l = l' ++ (x::l'')).
Proof.
  pose proof classic as tiers_exlc.
  intros.
  induction l.
  easy.
  destruct (tiers_exlc (x = a)).
  exists nil, l.
  simpl; now rewrite H0.
  destruct H.
  symmetry in H; contradiction.
  apply IHl in H.
  destruct H as [l' [l'' H1]].
  exists (a::l'), l''; simpl.
  now rewrite H1.
Qed.

Lemma In_incl : forall (x a : X) l, In x l -> In x (a::l).
Proof.
  intros.
  simpl.
  now right.
Qed.


Lemma In_neq : forall (x a : X) l' l'', x <> a -> In x  (l' ++ (a::l'')) -> In x  (l' ++ l'').
Proof.
  pose proof classic as tiers_exlc.
  intros.
  induction l'.
  simpl in H0.
  destruct H0.
  symmetry in H0.
  contradiction.
  now simpl.
  destruct (tiers_exlc (a0 = x)).
  now left.
  right.
  destruct H0.
  contradiction.
  now apply IHl' in H0. 
Qed.

Search "in_split".
Search "length".

Theorem classic_pigeonhole : forall l1 l2, pigeonhole l1 l2.
Proof.
  pose proof Nat.nlt_0_r as nlt_0.
  pose proof classic as tiers_exlc.
  pose proof Lt.lt_n_Sm_le as lt_S.
  pose proof Nat.nlt_ge as nlt_ge.
  pose proof Nat.le_antisymm as le_antisymm.
  pose proof Lt.lt_S_n as lt_S_n.
  pose proof app_length as app_length.

  unfold pigeonhole.
  intro.
  induction l1.
  easy.
  destruct (tiers_exlc (In a l1)).
  now constructor.
  intros.
  cut (repeats l1).
  now constructor.
  assert (exists l2' l2'', l2 = l2' ++ (a::l2'')).
  cut (In a l2).
  apply In_bisect.
  apply H0.
  now left.
  destruct H2 as [l2' [l2'' H2]].
  apply IHl1 with (l2 := l2'++l2'').
  intros.
  destruct (tiers_exlc (x=a)).
  rewrite H4 in H3; contradiction.
  rewrite H2 in H0.
  assert (In x (a :: l1)).
  now apply (In_incl x a) in H3.
  apply H0 in H5.
  now apply (In_neq x a).
  rewrite H2 in H1.
  simpl in H1.
  cut (length (l2' ++ a :: l2'') = S(length (l2' ++ l2''))).
  intro.
  rewrite H3 in H1.
  now apply lt_S_n in H1.
  (* il s'agissait d'un exercice du tuto introductif *)
  repeat rewrite app_length; now simpl.
Qed.

(* Lemma len_lemma : forall l1 l2 (a : X), (forall x, In x (a :: l1) -> In x l2) -> ~repeats l1 -> ~ In a l1 -> length l1 <= length l2. *)
(* Proof. *)
(*   pose proof classic as tiers_exlc. *)
(*   induction l1. *)
(*   intros. *)
(*   simpl. *)
(*   apply Nat.le_0_l. *)
(*   intros. *)
(*   assert (~ repeats l1 /\ ~In a l1). *)
(*   split. *)
(*   destruct (tiers_exlc (repeats l1)). *)
(*   cut (repeats (a :: l1)). *)
(*   intro; contradiction. *)
(*   constructor. *)
(*   now left. *)
(*   assumption. *)
(*   destruct (tiers_exlc (In a l1)). *)
(*   cut (In a0 (a :: l1)). *)
(*   intro; contradiction. *)
(*   apply In_incl. *)
(*   now left. *)
(*   assumption. *)
(* Admitted. *)


(* Theorem classic_pigeonhole : forall l1 l2, pigeonhole l1 l2. *)
(* Proof. *)
(*   pose proof Nat.nlt_0_r as nlt_0. *)
(*   pose proof classic as tiers_exlc. *)
(*   pose proof Lt.lt_n_Sm_le as lt_S. *)
(*   pose proof Nat.nlt_ge as nlt_ge. *)
(*   pose proof Nat.le_antisymm as le_antisymm. *)


(*   intros. *)
(*   unfold pigeonhole. *)
(*   intros. *)
(*   induction l1. *)
(*   simpl in H0. *)
(*   apply nlt_0 in H0; contradiction. *)
(*   intros. *)
(*   simpl in H0. *)
(*   destruct (tiers_exlc (length l2 < length l1)). *)
(*   destruct (tiers_exlc (forall x : X, In x l1 -> In x l2)). *)
(*   cut (repeats l1 \/ In a l1). *)
(*   now constructor. *)
(*   left. *)
(*   now apply (IHl1 H2 H1). *)
(*   assert (forall x : X, In x l1 -> In x l2). *)
(*   intros. *)
(*   apply (In_incl x a) in H3. *)
(*   now apply H in H3. *)
(*   contradiction. *)
(*   destruct (tiers_exlc (repeats l1)). *)
(*   cut (repeats l1 \/ In a l1). *)
(*   now constructor. *)
(*   now left. *)
(*   apply nlt_ge in H1. *)
(*   apply lt_S in H0. *)
(*   assert (length l1 = length l2) as len. *)
(*   apply le_antisymm. *)
(*   exact H1. *)
(*   exact H0. *)
(*   clear H0. *)
(*   clear H1. *)
(*   destruct (tiers_exlc (In a l1)). *)
(*   cut (repeats l1 \/ In a l1). *)
(*   now constructor. *)
(*   now right. *)


(* Qed. *)


  (* pose proof Lt.lt_n_Sm_le as lt_n_Sm_le. *)
  (* pose proof Lt.le_lt_or_eq as le_lt_or_eq. *)
  (* assert (forall n m : nat, n < S m -> n < m \/ n = m) as lt_S1. *)
  (* intros. *)
  (* apply le_lt_or_eq. *)
  (* now apply lt_n_Sm_le in H. *)
  (* clear lt_n_Sm_le. *)
  (* clear le_lt_or_eq. *)

  