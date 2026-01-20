Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [4%Z; -6%Z; -7%Z; -1%Z; 30%Z; -10%Z; -10%Z; -6%Z] (-6) 3024000.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step: 4 - 6 -7 -1 +30 -10 -10 -6 *)
    (* 4 - 6 = -2 *)
    (* -2 - 7 = -9 *)
    (* -9 - 1 = -10 *)
    (* -10 + 30 = 20 *)
    (* 20 - 10 = 10 *)
    (* 10 - 10 = 0 *)
    (* 0 - 6 = -6 *)
    reflexivity.
  - simpl.
    (* Compute the product step by step: 1 * 4 * -6 * -7 * -1 * 30 * -10 * -10 * -6 *)
    (* 1 * 4 = 4 *)
    (* 4 * -6 = -24 *)
    (* -24 * -7 = 168 *)
    (* 168 * -1 = -168 *)
    (* -168 * 30 = -5040 *)
    (* -5040 * -10 = 50400 *)
    (* 50400 * -10 = -504000 *)
    (* -504000 * -6 = 3024000 *)
    reflexivity.
Qed.