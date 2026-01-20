Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [2%Z; 10%Z; -5%Z; -6%Z; 30%Z; 0%Z; -8%Z; 30%Z; 10%Z; -8%Z; 2%Z] 57 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step-by-step *)
    (* 2 + 10 = 12 *)
    (* 12 + -5 = 7 *)
    (* 7 + -6 = 1 *)
    (* 1 + 30 = 31 *)
    (* 31 + 0 = 31 *)
    (* 31 + -8 = 23 *)
    (* 23 + 30 = 53 *)
    (* 53 + 10 = 63 *)
    (* 63 + -8 = 55 *)
    (* 55 + 2 = 57 *)
    reflexivity.
  - simpl.
    (* Multiplication will become zero because of 0 in list *)
    reflexivity.
Qed.