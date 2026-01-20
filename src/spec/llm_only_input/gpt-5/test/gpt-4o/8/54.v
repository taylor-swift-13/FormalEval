Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_list_1_4_8_16_32 :
  sum_product_spec (1 :: 4 :: 8 :: 16 :: 32 :: nil) (61, 16384).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.