Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [-10; 1; 10; 5; 9; -5; -5] 5 (-112500).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* compute sum = -10 + 1 + 10 + 5 + 9 - 5 - 5 = 5 *)
    reflexivity.
  - simpl.
    (* compute product = -10 * 1 * 10 * 5 * 9 * -5 * -5 = -112500 *)
    reflexivity.
Qed.