Require Import PeanoNat.
Require Import Nat.
Require Import Recdef.

Inductive bin : Set :=
| Zero : bin
| Double : bin -> bin
| DoubleOne : bin -> bin.

Locate "mod".
Search "<".
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
  | S m => if m mod 2 =? 0 then Double (f (S m/2))
          else DoubleOne (f (S m/2))
  end.

intros.
now apply lt_div2.
intros.
now apply lt_div2.

Fixpoint g (n : bin) :=
  match n with
  | Zero => 0
  | Double m => 2 * g m
  | DoubleOne m => (2*g m) + 1
  end.



