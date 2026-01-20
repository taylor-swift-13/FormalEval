Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [-6; 2; 4; -6; 0; 8; -10] (-8) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum step by step:
       0 + (-6) = -6
       -6 + 2 = -4
       -4 + 4 = 0
       0 + (-6) = -6
       -6 + 0 = -6
       -6 + 8 = 2
       2 + (-10) = -8 *)
    reflexivity.
  - simpl.
    (* Calculate product step by step:
       1 * -6 = -6
       -6 * 2 = -12
       -12 * 4 = -48
       -48 * -6 = 288
       288 * 0 = 0
       0 * 8 = 0
       0 * -10 = 0 *)
    reflexivity.
Qed.