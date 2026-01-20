Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [0%Z; 2%Z; 5%Z; 8%Z; -3%Z; -5%Z] 7 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum = 0 + 2 + 5 + 8 + (-3) + (-5) = 7 *)
    reflexivity.
  - simpl.
    (* product = 1 * 0 * 2 * 5 * 8 * (-3) * (-5) = 0 *)
    reflexivity.
Qed.