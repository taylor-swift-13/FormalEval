Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case_6_0_0_4_10_3_7_2_3 :
  sum_product_spec (6 :: 0 :: 0 :: 4 :: 10 :: 3 :: 7 :: 2 :: 3 :: nil) (35, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.