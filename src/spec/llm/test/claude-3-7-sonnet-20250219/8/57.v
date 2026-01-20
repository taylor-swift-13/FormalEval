Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_big_list :
  sum_product_spec [20%Z; 30%Z; 40%Z; 49%Z; 49%Z] 188 57624000.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 20 + 30 + 40 + 49 + 49 = 188 *)
    reflexivity.
  - simpl.
    (* 20 * 30 * 40 * 49 * 49 = 57624000 *)
    reflexivity.
Qed.