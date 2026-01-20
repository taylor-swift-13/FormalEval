Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [2%Z; 5%Z; -5%Z; 30%Z; 0%Z; -8%Z; 30%Z] 54 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 2 + 5 = 7 *)
    (* 7 + (-5) = 2 *)
    (* 2 + 30 = 32 *)
    (* 32 + 0 = 32 *)
    (* 32 + (-8) = 24 *)
    (* 24 + 30 = 54 *)
    reflexivity.
  - simpl.
    (* 1 * 2 = 2 *)
    (* 2 * 5 = 10 *)
    (* 10 * -5 = -50 *)
    (* -50 * 30 = -1500 *)
    (* -1500 * 0 = 0 *)
    reflexivity.
Qed.