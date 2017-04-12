Require Import PeanoNat.
Require Import Nat.
Require Import Recdef.

Inductive bin : Set :=
| Zero : bin
| Double : bin -> bin
| DoubleOne : bin -> bin.

Locate "mod".
Search "mod".
Print Nat.divmod.

Lemma lt_div2 : forall m, S m/2 < S m.
Proof.
  intro.
  pose proof PeanoNat.Nat.div_lt.
  pose proof Lt.neq_0_lt.
  pose proof Lt.lt_n_S.
  apply H.
  now apply H0.
  apply H1; now apply H0.
Qed.

Function f (n : nat) {measure  (fun (x:nat) => x)} :=
  match n with
  | 0 => Zero
  | n => if n mod 2 =? 0 then Double (f (n/2))
          else DoubleOne (f (n/2))
  end.

intros.
now apply lt_div2.
intros.
now apply lt_div2.
Defined.

Fixpoint g (n : bin) :=
  match n with
  | Zero => 0
  | Double m => 2 * g m
  | DoubleOne m => (2*g m) + 1
  end.


Theorem gf_id : forall n, g (f n) = n.
Proof.
  pose proof Nat.div_mod as div_mod.
  pose proof Nat.eqb_eq as eqb_eq.
  pose proof Nat.eqb_neq as eqb_neq.
  pose proof Nat.add_comm as add_comm.
  pose proof Nat.mod_upper_bound as mod_upper_bound.
  induction n.
  easy.
  functional induction (f (S n)).
  easy.
  unfold g; fold g.
  rewrite IHb.
  apply eqb_eq in e0.
  assert (n0 = 2 * (n0 / 2) + n0 mod 2).
  apply (div_mod n0 2).
  easy.
  rewrite e0 in H.
  rewrite (add_comm _ 0) in H.
  assert (forall p, 0 + p = p).
  easy.
  now rewrite H0 in H.
  unfold g; fold g.
  rewrite IHb.
  apply eqb_neq in e0.
  assert (n0 mod 2 = 1).
    case_eq (n0 mod 2).
    intro; contradiction.
    intro.
    assert (n0 mod 2 < 2).
    now apply (mod_upper_bound n0 2).
    intro.
    rewrite H0 in H.
    rewrite H0 in e0.
    inversion H.
    reflexivity.
    inversion H2.
    inversion H4.
  assert (n0 = 2 * (n0 / 2) + n0 mod 2).
  apply (div_mod n0 2).
  easy.
  now rewrite H in H0.
Qed.


Eval compute in f (g (Double Zero)).

Fixpoint length (n: bin) :=
  match n with
  | Zero => 1
  | Double m | DoubleOne m => 1 + length m
  end.

Print f_terminate.

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

Theorem gh_h : forall n, g (h n) = g n.
Proof.
  induction n.
  easy.
  unfold h; fold h.
  unfold g; fold g.
  rewrite <- IHn.
  case n.
  easy.
  unfold g; fold g.
  intro.
    case (h (Double b)).
    easy.
    easy.
    easy.
  unfold g; now fold g.
  unfold h; fold h.
  unfold g; fold g.
  now rewrite IHn.
Qed.

Search "mul".

Lemma hg_zero : forall n, h n = Zero <-> g n = 0.
Proof.
  pose proof Nat.neq_mul_0 as neq_zero.
  pose proof Nat.eq_mul_0 as eq_zero.
  pose proof Nat.add_comm as add_comm.
  split.
  (* => *)
  induction n.
  easy.
  simpl.
  case_eq n.
  easy.
  intros b Hn.
    case_eq (h (Double b)).
    intro.
    rewrite <- Hn.
    rewrite <- Hn in H; apply IHn in H. 
    now rewrite H.
    intros.
    now discriminate H0.
    intros.
    now discriminate H0.
  intros b Hn.
    case_eq (h (DoubleOne b)).
    intro.
    rewrite <- Hn.
    rewrite <- Hn in H; apply IHn in H. 
    now rewrite H.
    intros.
    now discriminate H0.
    intros.
    now discriminate H0.
    easy.
    (* <= *)
    induction n.
    easy.
    unfold g; fold g.
    intro.
    assert (g n = 0).
    rewrite eq_zero in H.
    destruct H.
    discriminate.
    assumption.
    apply IHn in H0.
    unfold h; fold h.
    rewrite H0.
    case n.
      easy.
      easy.
      easy.
    intros.
    simpl in H.
    rewrite (add_comm _ 1) in H.
    discriminate H.
Qed.

Lemma h_zero : forall n, h (Double n) = Zero <-> h n = Zero.
Proof.
  pose proof Nat.neq_mul_0 as neq_zero.
  pose proof Nat.eq_mul_0 as eq_zero.
  pose proof Nat.add_comm as add_comm.
  split.
  (* => *)
  intros.
  apply hg_zero in H.
  unfold g in H; fold g in H.
  apply eq_zero in H.
  assert (g n = 0).
  destruct H.
  discriminate.
  assumption.
  now rewrite <- hg_zero in H0.
  (* <= *)
  intros.
  apply hg_zero in H.
  assert (2 * g n = 0).
  apply eq_zero; now right.
  assert (g (Double n) = 0).
  unfold g; now fold g.
  now apply hg_zero.
Qed.

Lemma contrapositive: forall (P Q:Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  intro.
  apply H0; now apply H.
Qed.

Lemma hg_zero2 : forall n, h n <> Zero -> g n <> 0.
Proof.
  intro.
  assert (g n = 0 -> h n = Zero).
  apply hg_zero.
  now apply (contrapositive (g n = 0) _).
Qed.

Lemma h_zero2 : forall n, h (Double n) <> Zero -> h n <> Zero.
Proof.
  intro.
  assert (h n = Zero -> h (Double n) = Zero).
  now apply h_zero.
  now apply (contrapositive (h n = Zero)).
Qed.



Search "<".

Lemma fgh_h_notZero : forall n, h n <> Zero -> f (g (h n)) = h n.
Proof.
  pose proof Nat.mod_mul as mod_mul.
  pose proof Nat.mul_comm as mul_comm.
  pose proof Nat.add_comm as add_comm.
  pose proof Nat.neq_mul_0 as neq_zero.
  pose proof Nat.eqb_refl as eqb_refl.
  pose proof Nat.div_mod as div_mod.
  pose proof Nat.add_0_l as zero_plus.
  pose proof Nat.div_mul as div_mul.
  pose proof Nat.mod_add as mod_add.
  pose proof Nat.eqb_neq as eqb_neq.
  pose proof Nat.div_unique as div_unique.
  pose proof Lt.lt_n_S as lt_n_S.
  pose proof Nat.lt_succ_diag_r as gt_succ.

  intro.
  rewrite gh_h.
  induction n.
  easy.
  unfold g; fold g.
  assert (2 * (g n) mod 2 = 0).
  rewrite mul_comm.
  now apply mod_mul.
  rewrite f_equation.
  intro.
  assert (2 * g n <> 0).
  cut (g n <> 0).
  intro.
  now apply neq_zero.
  cut (h n <> Zero).
  apply hg_zero2.
  now apply h_zero2 in H0.
  rewrite H; rewrite eqb_refl.
  case_eq (2 * g n).
  intro.
  contradiction.
  intros.
  assert ((2 * g n)/2 = g n).
  rewrite (mul_comm 2 _).
  now apply div_mul.
  rewrite <- H2.
  rewrite H3.
  assert (h n <> Zero).
  now apply h_zero2 in H0.
  rewrite IHn.
  unfold h; fold h.
  case_eq n.
  intro.
  rewrite H5 in H4; simpl in H4.
  contradiction.
  intros.
  case_eq (h (Double b)).
  intro.
  rewrite <- H5 in H6; contradiction.
  easy.
  easy.
  easy.
  easy.
  intro.
  unfold g; fold g.
  unfold h; fold h.
  rewrite f_equation.
  assert ((2 * (g n) + 1) mod 2 <> 0).
  rewrite add_comm.
  rewrite mul_comm.
  now rewrite mod_add.
  apply eqb_neq in H0.
  rewrite H0.
  case_eq (2* g n +1).
  intro.
  rewrite add_comm in H1.
  discriminate H1.
  intros.
  assert (g n = (2 * g n + 1) / 2).
  apply (div_unique (2 * g n + 1) 2 (g n) 1).
  cut (0 < 1).
  apply lt_n_S.
  apply gt_succ.
  easy.
  rewrite <- H1.
  rewrite <- H2.
  case_eq (h n).
  intro.
  apply hg_zero in H3.
  now rewrite H3.
  intros.
  rewrite IHn.
  rewrite H3.
  reflexivity.
  rewrite H3; discriminate.
  intros.
  rewrite IHn.
  rewrite H3.
  reflexivity.
  rewrite H3; discriminate.
Qed.

Theorem fgh_h : forall n, f (g (h n)) = h n.
Proof.
  intro.
  case_eq (h n).
  easy.
  intros.
  assert (h n <> Zero).
  rewrite H; discriminate.
  rewrite <- H.
  now apply fgh_h_notZero.
  intros.
  assert (h n <> Zero).
  rewrite H; discriminate.
  rewrite <- H.
  now apply fgh_h_notZero.
Qed.
