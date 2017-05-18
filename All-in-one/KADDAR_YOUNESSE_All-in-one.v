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




(** *** b. Correction vis-à-vis de [permuted] **)
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

(************************)
(** * IV : Les entiers binaires  **)
(************************)

(** *** Projet Coq 2017 - Younesse Kaddar *)


Require Import PeanoNat.
Require Import Nat.
Require Import Recdef.

Inductive bin : Set :=
| Zero : bin
| Double : bin -> bin
| DoubleOne : bin -> bin.

(** ** 1. Programmer deux fonctions [f : N -> N2] et [g : N2 → N] telles que [g f = id] **)
(***********************)


Lemma lt_div2 : forall m, S m/2 < S m.
Proof.
  intro.
  apply PeanoNat.Nat.div_lt.
  now apply Lt.neq_0_lt.
  apply Lt.lt_n_S; now apply Lt.neq_0_lt.
Qed.

Function f (n : nat) {measure  (fun (x:nat) => x)} :=
  match n with
  | 0 => Zero
  | n => if n mod 2 =? 0 then Double (f (n/2))
          else DoubleOne (f (n/2))
  end.

(** Preuve de terminaison *)
intros n n0 teq teq0.
now apply lt_div2.
intros n n0 teq teq0.
now apply lt_div2.
Defined.

Fixpoint g (n : bin) :=
  match n with
  | Zero => 0
  | Double m => 2 * g m
  | DoubleOne m => (2*g m) + 1
  end.


(** ** 2. Prouver cette dernière égalité **)
(***********************)

Theorem gf_id : forall n, g (f n) = n.
Proof.
  induction n.
  - easy.
  - functional induction (f (S n)).
    + easy.
    + unfold g; fold g.
      rewrite IHb.
      apply Nat.eqb_eq in e0.
      assert (n0 = 2 * (n0 / 2) + n0 mod 2).
      { now apply (Nat.div_mod n0 2). }
      rewrite e0 in H.
      rewrite (Nat.add_comm _ 0) in H.
      assert (forall p, 0 + p = p).
      { easy. }
      now rewrite H0 in H.
    + unfold g; fold g.
      rewrite IHb.
      apply Nat.eqb_neq in e0.
      assert (n0 mod 2 = 1).
      {
        case_eq (n0 mod 2).
        * intros H; contradiction.
        * intro n1.
          assert (n0 mod 2 < 2).
          { now apply (Nat.mod_upper_bound n0 2). }
          intro H0.
          rewrite H0 in H.
          rewrite H0 in e0.
          inversion H.
          reflexivity.
          inversion H2.
          inversion H4.
      }
      assert (n0 = 2 * (n0 / 2) + n0 mod 2).
      {
        apply (Nat.div_mod n0 2).
        easy.
      }
      now rewrite H in H0.
Qed.

(** ** 3. Est-ce vrai que [f g = id] ? Si ce n’est pas le cas, programmer une fonction [h : N2 -> N2] telle que [forall x, g(x) = g(h(x))] et [f g h = h]. *)
(***********************)

(** Ce n'est effectivement pas le cas, comme l'illustre le contre-exemple suivant : *)

Eval compute in f (g (Double Zero)).



(** Si on voulait être taquin, on poserait [h = f g] (cf. la remarque introductive de la réponse suivante), mais pour rester dans l'esprit de l'exercice, prenons plutôt : *)


Fixpoint h (n : bin):=
  match n with
  | Zero => Zero
  | Double Zero => Zero
  | Double m  => let m' := (h m) in
                (match m' with
                 | Zero => Zero
                 | m' => Double m'
                 end)
  | DoubleOne m => DoubleOne (h m)
  end.


(** ** 4. Prouver ces deux dernières égalités. La difficulté de cette question dépend grandement de votre définition pour h. *)
(***********************)

(** L'allusion à la variation de difficulté selon la définition de [h] vient sûrement du fait qu'en prenant [h = f g], le résultat [f g h = h] est immédiat, puisqu'on a déjà montré que [g f = id] (la fonction [f g] est involutive).

 Mais ce serait de la triche : prenons
      - notre courage à deux mains
      - et le taureau par les cornes !
 *)

(** *** a. [g = g h]  *)

Theorem gh_h : forall n, g (h n) = g n.
Proof.
  induction n.
  easy.
  - unfold h; fold h.
    unfold g; fold g.
    rewrite <- IHn.
    case n.
    + easy.
    + unfold g; fold g.
      intros b.
      case (h (Double b)).
      * easy.
      * easy.
      * easy.
    + unfold g; now fold g.
  - unfold h; fold h.
    unfold g; fold g.
    now rewrite IHn.
Qed.


Lemma hg_zero : forall n, h n = Zero <-> g n = 0.
Proof.
  split.
  - (* => *)
    induction n.
    + easy.
    + simpl.
      case_eq n.
      * easy.
      * intros b Hn.
        case_eq (h (Double b)).
        -- intros H H0.
           rewrite <- Hn.
           rewrite <- Hn in H; apply IHn in H. 
           now rewrite H.
        -- intros b0 H H0.
           now discriminate H0.
        -- intros b0 H H0.
           now discriminate H0.
      * intros b Hn.
        case_eq (h (DoubleOne b)).
        -- intros H.
           rewrite <- Hn.
           rewrite <- Hn in H; apply IHn in H. 
           now rewrite H.
        -- intros b0 H H0.
           now discriminate H0.
        -- intros b0 H H0.
           now discriminate H0.
    + easy.
  (* <= *)
  - induction n.
    + easy.
    + unfold g; fold g.
      intro H.
      assert (g n = 0).
      {
        rewrite Nat.eq_mul_0 in H.
        destruct H.
        discriminate.
        assumption.
      }
      apply IHn in H0.
      unfold h; fold h.
      rewrite H0.
      case n.
      * easy.
      * easy.
      * easy.
    + intros H.
      simpl in H.
      rewrite (Nat.add_comm _ 1) in H.
      discriminate H.
Qed.

Lemma h_zero : forall n, h (Double n) = Zero <-> h n = Zero.
Proof.
  split.
  - (* => *)
    intro H.
    apply hg_zero in H.
    unfold g in H; fold g in H.
    apply Nat.eq_mul_0 in H.
    assert (g n = 0).
    destruct H.
    discriminate.
    assumption.
    now rewrite <- hg_zero in H0.
  - (* <= *)
    intro H.
    apply hg_zero in H.
    assert (2 * g n = 0).
    { apply Nat.eq_mul_0; now right. }
    assert (g (Double n) = 0).
    unfold g; now fold g.
    now apply hg_zero.
Qed.

Lemma contrapositive: forall (P Q:Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H H0.
  intro H1.
  apply H0; now apply H.
Qed.

Lemma hg_zero2 : forall n, h n <> Zero -> g n <> 0.
Proof.
  intro n.
  assert (g n = 0 -> h n = Zero).
  { apply hg_zero. }
  now apply (contrapositive (g n = 0) _).
Qed.

Lemma h_zero2 : forall n, h (Double n) <> Zero -> h n <> Zero.
Proof.
  intro n.
  assert (h n = Zero -> h (Double n) = Zero).
  { now apply h_zero. }
  now apply (contrapositive (h n = Zero)).
Qed.

(** *** b. [f g h = h]  *)

Lemma fgh_h_notZero : forall n, h n <> Zero -> f (g (h n)) = h n.
Proof.
  intros n.
  rewrite gh_h.
  induction n.
  - easy.
  - unfold g; fold g.
    assert (2 * (g n) mod 2 = 0).
    {
      rewrite Nat.mul_comm.
      now apply Nat.mod_mul.
    }
    rewrite f_equation.
    intro H0.
    assert (2 * g n <> 0).
    {
      cut (g n <> 0).
      {
        intro H1.
        now apply Nat.neq_mul_0.
      }
      cut (h n <> Zero).
      { apply hg_zero2. }
      now apply h_zero2 in H0.
    }
    rewrite H; rewrite Nat.eqb_refl.
    case_eq (2 * g n).
    + intro H2.
      contradiction.
    + intros n0 H2.
      assert ((2 * g n)/2 = g n).
      {
        rewrite (Nat.mul_comm 2 _).
        now apply Nat.div_mul.
      }
      rewrite <- H2.
      rewrite H3.
      assert (h n <> Zero).
      { now apply h_zero2 in H0. }
      rewrite IHn.
      unfold h; fold h.
      case_eq n.
      * intros H5.
        rewrite H5 in H4; simpl in H4.
        contradiction.
      * intros b H5.
        case_eq (h (Double b)).
        -- intro H6.
           rewrite <- H5 in H6; contradiction.
        -- easy.
        -- easy.
      * easy.
      * easy.
  - intro H.
    unfold g; fold g.
    unfold h; fold h.
    rewrite f_equation.
    assert ((2 * (g n) + 1) mod 2 <> 0).
    {
      rewrite Nat.add_comm.
      rewrite Nat.mul_comm.
      now rewrite Nat.mod_add.
    }
    apply Nat.eqb_neq in H0.
    rewrite H0.
    case_eq (2* g n +1).
    + intro H1.
      rewrite Nat.add_comm in H1.
      discriminate H1.
    + intros n0 H1.
      assert (g n = (2 * g n + 1) / 2).
      {
        apply (Nat.div_unique (2 * g n + 1) 2 (g n) 1).
        cut (0 < 1).
        { apply Lt.lt_n_S. }
        apply Nat.lt_succ_diag_r.
        easy.
      }
      rewrite <- H1.
      rewrite <- H2.
      case_eq (h n).
      * intro H3.
        apply hg_zero in H3.
        now rewrite H3.
      * intros b H3.
        rewrite IHn.
        rewrite H3.
        reflexivity.
        rewrite H3; discriminate.
      * intros b H3.
        rewrite IHn.
        rewrite H3.
        reflexivity.
        rewrite H3; discriminate.
Qed.

Theorem fgh_h : forall n, f (g (h n)) = h n.
Proof.
  intro n.
  case_eq (h n).
  - easy.
  - intros b H.
    assert (h n <> Zero).
    { rewrite H; discriminate. }
    rewrite <- H.
    now apply fgh_h_notZero.
  - intros.
    assert (h n <> Zero).
    { rewrite H; discriminate. }
    rewrite <- H.
    now apply fgh_h_notZero.
Qed.

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

-- [embedded_implies_linked : forall l1 l2, embedded X l1 l2 -> linked l1 l2]

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



