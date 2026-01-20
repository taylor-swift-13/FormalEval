Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_1 :
  sum_product_spec [1%Z; 3%Z; 20%Z; 30%Z; 30%Z] 84 54000.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 1 + 3 + 20 + 30 + 30 = 84 *)
    reflexivity.
  - simpl.
    (* 1 * 3 * 20 * 30 * 30 = 54000 *)
    reflexivity.
Qed.