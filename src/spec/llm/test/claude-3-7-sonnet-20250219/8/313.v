Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [10%Z; -5%Z; 30%Z; -10%Z; 0%Z; -8%Z; 11%Z; 30%Z; 10%Z; 30%Z; -8%Z; -8%Z] 82 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sums stepwise: *)
    (* 10 + (-5) = 5 *)
    (* 5 + 30 = 35 *)
    (* 35 + (-10) = 25 *)
    (* 25 + 0 = 25 *)
    (* 25 + (-8) = 17 *)
    (* 17 + 11 = 28 *)
    (* 28 + 30 = 58 *)
    (* 58 + 10 = 68 *)
    (* 68 + 30 = 98 *)
    (* 98 + (-8) = 90 *)
    (* 90 + (-8) = 82 *)
    reflexivity.
  - simpl.
    (* Multiplication by zero anywhere leads to zero product *)
    reflexivity.
Qed.