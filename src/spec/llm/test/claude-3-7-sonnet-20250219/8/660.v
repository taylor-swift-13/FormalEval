Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [6%Z; 20%Z; 1%Z; 0%Z; 4%Z; 7%Z; 3%Z; 7%Z; 2%Z] 50 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* calculate sum: 6 + 20 + 1 + 0 + 4 + 7 + 3 + 7 + 2 = 50 *)
    reflexivity.
  - simpl.
    (* calculate product: 6 * 20 * 1 * 0 * 4 * 7 * 3 * 7 * 2 = 0 because of zero factor *)
    reflexivity.
Qed.