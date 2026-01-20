Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [0%Z; 20%Z; -1%Z; 1%Z; -1%Z; 30%Z; 1%Z] 50 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 0 + 20 + (-1) + 1 + (-1) + 30 + 1 = 50 *)
    reflexivity.
  - simpl.
    (* Compute product: 1 * 0 * 20 * (-1) * 1 * (-1) * 30 * 1 = 0 *)
    reflexivity.
Qed.