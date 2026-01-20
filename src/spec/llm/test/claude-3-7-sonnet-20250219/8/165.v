Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [2; 10; -5; 30; 0; -8; 10; -5] 34 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step *)
    (* 2 + 10 = 12 *)
    (* 12 + (-5) = 7 *)
    (* 7 + 30 = 37 *)
    (* 37 + 0 = 37 *)
    (* 37 + (-8) = 29 *)
    (* 29 + 10 = 39 *)
    (* 39 + (-5) = 34 *)
    reflexivity.
  - simpl.
    (* Compute the product step by step *)
    (* 1 * 2 = 2 *)
    (* 2 * 10 = 20 *)
    (* 20 * (-5) = -100 *)
    (* -100 * 30 = -3000 *)
    (* -3000 * 0 = 0 *)
    (* 0 * (-8) = 0 *)
    (* 0 * 10 = 0 *)
    (* 0 * (-5) = 0 *)
    reflexivity.
Qed.