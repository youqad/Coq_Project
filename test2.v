Require Import List.
Require Import PeanoNat.

Locate "<=".
Print le.

SearchAbout "eqb".
SearchAbout "nth".
Search "fold".
Search "ltb".


Fixpoint insert (x:nat) (l: list nat) : list nat :=
  match l with
  | nil => x::nil
  | h::t => (match Nat.ltb h x with
            | true => h::(insert x t)
            | false => x::l
            end)
  end.

Fixpoint sort (l: list nat) : list nat :=
    match l with
        | nil => nil
        | h::t => insert h (sort t)
    end.

(* Definition is_sorted (l:list nat) : Prop := forall x y, x<y -> y < length l -> nth x l 0 <= nth y l 0. *)

Print List.hd.
Print bool.

Inductive is_sorted : list nat -> Prop :=
| nil_sorted : is_sorted nil
| sing_sorted : forall x, is_sorted (x :: nil)
| list_sorted : forall h h' t, le h h' -> is_sorted (h'::t) -> is_sorted (h::(h'::t)).

Print fold_left.
Print nth.

Definition count (l:list nat) (x:nat) : nat := fold_left (fun c h => if Nat.eqb h x then c+1 else c) l 0.


Definition are_shuffled (l:list nat) (l':list nat): Prop 
  := forall x y, x<y -> x < length l -> y < length l' -> count l x = count l' y.

Lemma is_sorted_inv : forall l a, is_sorted (a::l) -> is_sorted l.
Proof.
  intros.
  inversion H.
  constructor.
  assumption.
Qed.

Search "nlt".
Print Nat.ltb_lt.
Locate "<?".
Print lt.

(*
    pose proof eq_nat_decide.
    Search eq_nat.
    pose proof eq_nat_is_eq.
*)
(* Lemma well_sorted : forall (l : list nat), is_sorted (sort l). *)
(* Proof. *)
(*     intro l. *)
(*     induction l. *)
(*      - (* l = nil *) *)
(*      easy. *)
(*      - (* l' = a::l *) *)
(*        simpl. *)
(*        (* rewrite → IHl. *) *)
(*        (* reflexivity. *) *)
(* Admitted. *)

Lemma insert_hd : forall l x, is_sorted l -> hd 0 (insert x l) = x \/ hd 0 (insert x l) = hd 0 l.
Proof.
  intros.
  inversion H.
  simpl; now left.
  simpl.
  destruct (x0 <? x).
  now right.
  now left.
  simpl.
  case (h <? x).
  now right.
  now left.
Qed.

Lemma insert_sort : forall (l: list nat), (is_sorted l) -> forall (x : nat), is_sorted (insert x l).
Proof.
  pose proof Nat.ltb_lt as ltb_lt.
  pose proof Nat.ltb_nlt as ltb_nlt.
  pose proof Nat.lt_le_incl as le_implies_lt.
  pose proof Nat.nlt_ge as nlt_ge.
  intros.
  induction l.
  simpl; constructor.
  (* -- is_sorted (insert x l) -- *)
  assert (is_sorted (insert x l)).
  apply is_sorted_inv in H.
  now apply IHl in H.
  (* ---------------------------- *)
  (* -------- a <= hd l --------- *)
  assert (l = nil \/ le a (hd 0 l)).
  inversion H.
  now left.
  now right.
  (* ---------------------------- *)
  simpl.
  case_eq (a <? x).
  (* --- a < x ----- *)
  apply is_sorted_inv in H.
  intro.
  apply ltb_lt in H2.
  apply le_implies_lt in H2.
  apply (insert_hd l x) in H.
  assert (le a (hd 0 (insert x l))).
  destruct H as [G1 | G2].
  now rewrite <- G1 in H2. 
  destruct l.
  now simpl.
  inversion H1.
  discriminate H.
  now rewrite G2.
  apply list_sorted with (t:= tl (insert x l)) in H3.
  destruct (insert x l).
  constructor.
  now simpl in H3.
  destruct (insert x l).
  constructor.
  now simpl in H3.
  (* ------ ~ (a < x) ------ *)
  intro.
  apply ltb_nlt in H2.
  apply nlt_ge in H2.
  now constructor.
Qed.

Search "eqb".
(* pose proof eq_nat_decide. *)
(* pose proof eq_nat_is_eq. *)

Lemma count_lemma : forall l' k x, fold_left (fun c h : nat => if h =? x then c + 1 else c) l' (1+k) = 1 + fold_left (fun c h : nat => if h =? x then c + 1 else c) l' k.
Proof.
  induction l'.
  now simpl.
  intros.
  simpl.
  destruct (a =? x).
  simpl; rewrite IHl'; simpl.
  reflexivity.
  apply IHl'.
Qed.

Lemma count_insert : forall (x: nat) (l : list nat), count (insert x l) x = S (count l x).
Proof.
  pose proof Nat.eqb_eq as eqb_eq.
  pose proof Nat.eqb_neq as eqb_neq.
  pose proof Nat.eqb_refl as eqb_refl.
  pose proof Nat.lt_neq as lt_neq.
  pose proof Nat.ltb_lt as ltb_lt.
  assert (forall n m : nat, (n <? m) = true -> n <> m) as ltb_neq.
  intros.
  apply lt_neq.
  now apply ltb_lt.
  clear lt_neq; clear ltb_lt.
  unfold count.
  induction l.
  simpl.
  now rewrite eqb_refl.
  repeat simpl.
  case_eq (a <? x).
  intro.
  apply ltb_neq in H.
  rewrite <- (eqb_neq a x) in H.
  simpl; rewrite H; simpl.
  now apply IHl.
  intro.
  case_eq (a =? x).
  intro.
  repeat simpl.
  rewrite eqb_refl; rewrite H0.
  simpl.
  apply (count_lemma l 1 x).
  intro.
  simpl.
  rewrite eqb_refl; rewrite H0.
  simpl.
  apply (count_lemma l 0 x).
 Qed.

Lemma sort_shuffled : forall (l : list nat), are_shuffled (sort l).
Proof.
  
Qed.