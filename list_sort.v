(************************)
(** * III : Trier une liste  **)
(************************)

(** *** Projet Coq 2017 - Younesse Kaddar *)


Require Import List.
Require Import PeanoNat.




(** ** 1. Choisir un algorithme de tri et implémenter la fonction [sort] en utilisant cet algorithme **)
(***********************)

(** J'ai choisi le tri par insertion. *)

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

(** ** 2. Définir un prédicat [sorted] qui certifie qu'une liste est triée **)
(***********************)

(** Le prédicat [sorted] m'a donné du fil à retordre : le définir avec un [Fixpoint] était une voie sans issue.

Le prédicat inductif suivant s'est par contre révélé être bien utile. *)

Inductive sorted : list nat -> Prop :=
| nil_sorted : sorted nil
| sing_sorted : forall x, sorted (x :: nil)
| list_sorted : forall h h' t, le h h' -> sorted (h'::t) -> sorted (h::(h'::t)).

(** ** 2. Définir un prédicat binaire [permuted] qui certifie qu’une liste est la permutation d'une autre **)
(***********************)

(** Pour le prédicat [permuted], j'ai utilisé un prédicat auxiliaire [count] dénombrant le nombre d'occurrences d'un élément dans une liste. *)

Definition count (l:list nat) (x:nat) : nat :=
  fold_left (fun c h => if Nat.eqb h x then c+1 else c) l 0.

Definition permuted (l:list nat) (l':list nat): Prop := forall x, count l x = count l' x.


(** ** 3. Prouver que votre algorithme de tri est correct vis-à-vis de ces deux prédicats **)
(***********************)

(** *** a. Correction vis-à-vis de [sorted] **)
(***********************)

(** Je vais avoir besoin de deux petits lemmes :
    - le lemme d'affaiblissement [is_sorted_inv]
    - le lemme [insert_hd], qui donne une alternative concernant la tête de [insert x l] dès que [l] est triée

 *)

Lemma is_sorted_inv : forall l a, sorted (a::l) -> sorted l.
Proof.
  intros l a H.
  inversion H.
  constructor.
  assumption.
Qed.


Lemma insert_hd : forall l x, sorted l -> hd 0 (insert x l) = x \/ hd 0 (insert x l) = hd 0 l.
Proof.
  intros l x H.
  inversion H.
  - (* Cas de base : l = nil *)
    simpl; now left.
  - (* l = x0::nil *)
    simpl.
    destruct (x0 <? x).
    + now right.
    + now left.
  - (* l = h :: h' :: t *)
    simpl.
    case (h <? x).
    + now right.
    + now left.
Qed.

Search "lt_le_incl".

Lemma insert_sort : forall (l: list nat), (sorted l) -> forall (x : nat), sorted (insert x l).
Proof.
  intros l H x.
  induction l.
  - (* l = nil *)
    simpl; constructor.
  - (* l <- a :: l *)
    assert (sorted (insert x l)).
    {
      apply is_sorted_inv in H.
      now apply IHl in H.
    }
    assert (l = nil \/ le a (hd 0 l)). (* a <= hd l *)
    {
      inversion H.
      now left.
      now right.
    }
  simpl.
  case_eq (a <? x).
  + (* a < x *)
    apply is_sorted_inv in H.
    intro H2.
    apply Nat.ltb_lt in H2.
    apply Nat.lt_le_incl in H2.
    apply (insert_hd l x) in H.
    assert (le a (hd 0 (insert x l))).
    {
      destruct H as [G1 | G2].
      -- now rewrite <- G1 in H2.
      -- destruct l.
         ++ now simpl.
         ++ inversion H1.
            discriminate H.
            now rewrite G2.
  }
    apply list_sorted with (t:= tl (insert x l)) in H3.
    destruct (insert x l).
    constructor. now simpl in H3.
    destruct (insert x l).
    constructor. now simpl in H3.
  + (* ~ (a < x) *)
    intros H2.
    apply Nat.ltb_nlt in H2.
    apply Nat.nlt_ge in H2.
    now constructor.
Qed.




Theorem well_sorted : forall (l : list nat), sorted (sort l).
Proof.
    intro l.
    induction l.
    - simpl.
      constructor.
    - simpl.
      now apply (insert_sort (sort l)) with (x:=a) in IHl.
Qed.




(** *** a. Correction vis-à-vis de [permuted] **)
(***********************)


Lemma count_lemma : forall l' k x,
    fold_left (fun c h : nat => if h =? x then c + 1 else c) l' (1+k) =
    1 + fold_left (fun c h : nat => if h =? x then c + 1 else c) l' k.
Proof.
  induction l'.
  - now simpl.
  - intros k x.
    simpl.
    destruct (a =? x).
    + simpl; rewrite IHl'; simpl.
    reflexivity.
    + apply IHl'.
Qed.

Lemma count_insert : forall (x: nat) (l : list nat), count (insert x l) x = S (count l x).
Proof.
  assert (forall n m : nat, (n <? m) = true -> n <> m) as ltb_neq.
  {
    intros n m H.
    apply Nat.lt_neq.
    now apply Nat.ltb_lt.
  }
  unfold count.
  induction l.
  - simpl.
    now rewrite Nat.eqb_refl.
  - repeat simpl.
    case_eq (a <? x).
    + intro H.
      apply ltb_neq in H.
      rewrite <- (Nat.eqb_neq a x) in H.
      simpl; rewrite H; simpl.
      now apply IHl.
    + intro H.
      case_eq (a =? x).
      * intro H0.
        repeat simpl.
        rewrite Nat.eqb_refl; rewrite H0.
        simpl.
        apply (count_lemma l 1 x).
      * intro H0.
        simpl.
        rewrite Nat.eqb_refl; rewrite H0.
        simpl.
        apply (count_lemma l 0 x).
Qed.

Lemma count_insert2 : forall (x y: nat) (l : list nat), y <> x -> count (insert y l) x = count l x.
Proof.
  assert (forall n m : nat, (n <? m) = true -> n <> m) as ltb_neq.
  {
    intros n m H.
    apply Nat.lt_neq.
    now apply Nat.ltb_lt.
  }
  unfold count.
  induction l.
  - simpl.
    intro H.
    apply Nat.eqb_neq in H.
    now rewrite H.
  - intro G.
  repeat simpl.
  case_eq (a =? x).
    + intro H.
      simpl.
      case_eq (a <? y).
      * intro H0.
        simpl; rewrite H.
        pose proof (count_lemma l 0 x) as count_lemma1.
        simpl in count_lemma1.
        rewrite count_lemma1.
        pose proof (count_lemma (insert y l) 0 x) as count_lemma2.
        simpl in count_lemma2.
        rewrite count_lemma2.
        now rewrite IHl.
      * intro H0.
        simpl; rewrite H.
        apply Nat.eqb_neq in G; rewrite G.
        now simpl.
    + intro H.
      case_eq (a <? y).
      * intro H0.
        simpl; rewrite H.
        now apply IHl.
      * intros H0.
        simpl.
        rewrite H.
        apply Nat.eqb_neq in G; now rewrite G.
Qed.


Theorem sort_permuted : forall (l : list nat), permuted l (sort l).
Proof.
  induction l.
  - easy.
  - unfold permuted.
    simpl.
    intro x.
    case (Nat.eq_dec x a).
    + intros e.
      rewrite e.
      rewrite count_insert.
      rewrite <- IHl.
      unfold count; simpl; rewrite Nat.eqb_refl.
      apply (count_lemma l 0 a).
    + intro n.
      rewrite count_insert2.
      assert (count (a::l) x = count l x).
      {
        unfold count.
        simpl.
        apply Nat.eqb_neq in n; rewrite Nat.eqb_sym in n.
        now rewrite n.
      }
      rewrite H.
      now rewrite IHl.
      now apply Nat.neq_sym in n.
Qed.

