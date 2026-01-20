Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec [2%Z; 10%Z; -5%Z; 3%Z; 0%Z; -8%Z; 10%Z] 12 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: 0 + 2 = 2, 2 + 10 = 12, 12 + (-5) = 7, 7 + 3 = 10, 10 + 0 = 10, 10 + (-8) = 2, 2 + 10 = 12 *)
    reflexivity.
  - simpl.
    (* Calculate product: 1 * 2 = 2, 2 * 10 = 20, 20 * -5 = -100, -100 * 3 = -300, -300 * 0 = 0, 0 * -8 = 0, 0 * 10 = 0 *)
    reflexivity.
Qed.