Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [4%Z; 0%Z; -6%Z; -10%Z; 4%Z; 2%Z] (-6) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: 4 + 0 = 4, 4 + (-6) = -2, -2 + (-10) = -12, -12 + 4 = -8, -8 + 2 = -6 *)
    reflexivity.
  - simpl.
    (* Calculate product: 1 * 4 = 4, 4 * 0 = 0, 0 * -6 = 0, 0 * -10 = 0, 0 * 4 = 0, 0 * 2 = 0 *)
    reflexivity.
Qed.