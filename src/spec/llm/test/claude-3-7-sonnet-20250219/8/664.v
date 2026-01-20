Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_zeros_and_negatives :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -6%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-20%Z) 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum step-by-step *)
    (* 0 + 0 + 0 + 0 + 0 = 0 *)
    (* 0 + (-6) = -6 *)
    (* -6 + 1 = -5 *)
    (* -5 + (-1) = -6 *)
    (* -6 + (-6) = -12 *)
    (* -12 + (-8) = -20 *)
    (* -20 + zeros = -20 *)
    reflexivity.
  - simpl.
    (* Calculate product step-by-step *)
    (* 1 * 0 = 0 immediately *)
    reflexivity.
Qed.