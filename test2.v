Require Import List.

Locate "<=".
Print le.

SearchAbout "eqb".
SearchAbout "nth".
Search "fold".


Fixpoint insert (x:nat) (l: list nat) : list nat :=
    match l with
        | nil => x::nil
        | h::t => if Nat.ltb x h then x::l else h::(insert x t) 
    end.

Fixpoint sort (l: list nat) : list nat :=
    match l with
        | nil => nil
        | h::t => insert h (sort t)
    end.

Definition is_sorted (l:list nat) : Prop := forall x y, x<y -> y < length l -> nth x l 0 <= nth y l 0.


Definition count (l:list nat) (x:nat) : nat := fold_left (fun c t => if Nat.eqb t (nth x l 0) then c+1 else c) l 0.


Definition are_shuffled (l:list nat) (l':list nat): Prop 
:= forall x y, x<y -> x < length l -> y < length l' -> count l x = count l' y.

(*
    pose proof eq_nat_decide.
    Search eq_nat.
   o pose proof eq_nat_is_eq.
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

Lemma insert_sort : forall (l: list nat), (is_sorted l) -> forall (x : nat), is_sorted (insert x l).
Proof.
  intro l.
  induction l.
  - (* l = nil *)
    intros.
    simpl.
    unfold is_sorted.
    intros x0 y H0 H1.
    simpl in H1.
    unfold lt in H1.
    inversion H1.
    subst.
    inversion H0.
    inversion H3.
  -  (* l' = a::l *)
    intros H x.
    unfold insert x.

Lemma count_insert : forall (x: nat) (l : list nat), count (insert x l) = S (count l x).


Lemma sort_shuffled : forall (l : list nat), are_shuffled (sort l).
Proof.

Qed.