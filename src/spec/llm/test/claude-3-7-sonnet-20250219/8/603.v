Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_big_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 31; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    95 31.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum 50 ones plus 31 plus 13 ones = 95 *)
    reflexivity.
  - simpl.
    (* product is 31, since all others are 1 *)
    reflexivity.
Qed.