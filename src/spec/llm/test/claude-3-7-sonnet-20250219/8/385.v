Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [-10%Z; 0%Z; 7%Z; 0%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] 7 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: -10 + 0 + 7 + 0 + 2 + 2 + 2 + 2 + 2 = 7 *)
    reflexivity.
  - simpl.
    (* Calculate product: (-10) * 0 * 7 * 0 * 2 * 2 * 2 * 2 * 2 = 0 *)
    reflexivity.
Qed.