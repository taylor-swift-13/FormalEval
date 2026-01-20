Require Import Coq.Lists.List Coq.Init.Nat.
Import ListNotations.

Fixpoint fact (n:nat) : nat := match n with 0=>1 | S k => n * fact k end.

Definition brazilian_factorial_impl (n:nat) : nat :=
  fold_right mult 1 (map fact (seq 1 n)).

Example brazilian_factorial_impl_4: brazilian_factorial_impl 4%nat = 288%nat.
Proof. reflexivity. Qed.

Definition brazilian_factorial_spec (n : nat) (output : nat) : Prop :=
  output = brazilian_factorial_impl n.


