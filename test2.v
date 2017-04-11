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
  := forall x, count l x = count l' x.

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

Lemma count_insert2 : forall (x y: nat) (l : list nat), y <> x -> count (insert y l) x = count l x.
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
  intro.
  apply eqb_neq in H.
  now rewrite H.
  intro G.
  repeat simpl.
  case_eq (a =? x).
  intro.
  simpl.
  (* apply eqb_eq in H. *)
  (* rewrite <- H in G; apply eqb_neq in G. *)
  simpl.
    case_eq (a <? y).
    intro.
    simpl; rewrite H.
    pose proof (count_lemma l 0 x) as count_lemma1.
    simpl in count_lemma1.
    rewrite count_lemma1.
    pose proof (count_lemma (insert y l) 0 x) as count_lemma2.
    simpl in count_lemma2.
    rewrite count_lemma2.
    now rewrite IHl.
    intro.
    simpl; rewrite H.
    apply eqb_neq in G; rewrite G.
    now simpl.
  (* --- *)
  intro.
    case_eq (a <? y).
    intro.
    simpl; rewrite H.
    now apply IHl.
    intro.
    simpl.
    rewrite H.
    apply eqb_neq in G; now rewrite G.
Qed.

Search "neq".

Lemma sort_shuffled : forall (l : list nat), are_shuffled l (sort l).
Proof.
  pose proof Nat.eqb_eq as eqb_eq.
  pose proof Nat.eqb_neq as eqb_neq.
  pose proof Nat.eqb_refl as eqb_refl.
  pose proof Nat.eq_dec as eq_dec.
  pose proof Nat.eqb_sym as eqb_sym.
  pose proof Nat.neq_sym as neq_sym.
  induction l.
  easy.
  unfold are_shuffled.
  simpl.
  intros.
  case (eq_dec x a).
  intro.
  rewrite e.
  rewrite count_insert.
  rewrite <- IHl.
  unfold count; simpl; rewrite eqb_refl.
  apply (count_lemma l 0 a).
  intro.
  rewrite count_insert2.
  assert (count (a::l) x = count l x).
  unfold count.
  simpl.
  apply eqb_neq in n; rewrite eqb_sym in n.
  now rewrite n.
  rewrite H.
  now rewrite IHl.
  now apply neq_sym in n. 
Qed.


Lemma well_sorted : forall (l : list nat), is_sorted (sort l).
Proof.
    intro l.
    induction l.
    simpl.
    constructor.
    simpl.
    now apply (insert_sort (sort l)) with (x:=a) in IHl.
Qed.