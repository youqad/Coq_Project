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

Fixpoint h (n : bin) :=
  match n with
  | Zero => Zero
  | Double Zero => Zero
  | Double m  => Double (h m)
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
  unfold g; now fold g.
  unfold g; now fold g.
  unfold h; fold h.
  unfold g; fold g.
  now rewrite IHn.
Qed.

