Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_nonempty_list :
  sum_product_spec (1 :: 8 :: 3 :: 20 :: 30 :: nil) (62, 14400).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.