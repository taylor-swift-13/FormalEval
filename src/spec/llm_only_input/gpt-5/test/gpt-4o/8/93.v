Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_list_1_4_16_32 :
  sum_product_spec (cons 1 (cons 4 (cons 16 (cons 32 nil)))) (53, 2048).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.