Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [2%Z; 10%Z; -5%Z; 30%Z; 0%Z; -7%Z; -7%Z; -11%Z; 10%Z; 30%Z] 52 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step-by-step *)
    reflexivity.
  - simpl.
    (* Compute the product step-by-step *)
    reflexivity.
Qed.