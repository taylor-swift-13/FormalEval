Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [1%Z; 2%Z; -8%Z; 8%Z; 8%Z; -6%Z] 5 6144.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum stepwise: (((((0 + 1) + 2) + -8) + 8) + 8) + -6 = 5 *)
    reflexivity.
  - simpl.
    (* Compute product stepwise:
       (((((1 * 1) * 2) * -8) * 8) * 8) * -6 =
       1 * 2 = 2; 2 * -8 = -16; -16 * 8 = -128; -128 * 8 = -1024; -1024 * -6 = 6144 *)
    reflexivity.
Qed.