Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example test_sum_product : sum_product_spec [2; 3; 13; 7; 11; 13; 2; 1] (52, 156156).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.