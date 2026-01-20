Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_pos_mix :
  sum_product_spec [-1%Z; 1%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 1 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: -1 + 1 + 1 + 0 + 0 + 0 + 0 + 0 = 1 *)
    reflexivity.
  - simpl.
    (* Compute product: (-1) * 1 * 1 * 0 * 0 * 0 * 0 * 0 = 0 *)
    reflexivity.
Qed.