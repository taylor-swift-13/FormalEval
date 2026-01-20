Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_input : 
  sum_product_spec [0%Z; 2%Z; 4%Z; 7%Z; -3%Z; -5%Z; -5%Z; 2%Z] 2 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step: 0 + 2 + 4 + 7 + (-3) + (-5) + (-5) + 2 *)
    reflexivity.
  - simpl.
    (* Compute the product step by step: 1 * 0 * 2 * 4 * 7 * (-3) * (-5) * (-5) * 2 
       Since there is a zero, product is 0 *)
    reflexivity.
Qed.