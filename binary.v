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
