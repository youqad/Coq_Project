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
  | S m => if (S m) mod 2 =? 0 then Double (f (S m/2))
          else DoubleOne (f (S m/2))
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
  assert (S m = 2 * (S m / 2) + S m mod 2).
  apply (div_mod (S m) 2).
  easy.
  rewrite e0 in H.
  rewrite (add_comm _ 0) in H.
  assert (forall p, 0 + p = p).
  easy.
  now rewrite H0 in H.
  unfold g; fold g.
  rewrite IHb.
  apply eqb_neq in e0.
  assert (S m mod 2 = 1).
    case_eq (S m mod 2).
    intro; contradiction.
    intro.
    assert (S m mod 2 < 2).
    now apply (mod_upper_bound (S m) 2).
    intro.
    rewrite H0 in H.
    rewrite H0 in e0.
    inversion H.
    reflexivity.
    inversion H2.
    inversion H4.
  assert (S m = 2 * (S m / 2) + S m mod 2).
  apply (div_mod (S m) 2).
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
    

Lemma fgh_h : forall n, h n <> Zero -> f (g (h n)) = h n.
Proof.
  pose proof Nat.mod_mul as mod_mul.
  pose proof Nat.mul_comm as mul_comm.
  pose proof Nat.neq_mul_0 as neq_zero.
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

  functional induction (f (2 * (g n))).

  easy.
  rewrite H.
  case_eq n.
  now simpl.
  intros.
  simpl.
  rewrite <- H.
  rewrite IHn.
  unfold h.
  case n.
  easy.
  unfold g; now fold g.
  unfold g; now fold g.
  unfold h; fold h.
  unfold g; fold g.
  now rewrite IHn.
Qed.