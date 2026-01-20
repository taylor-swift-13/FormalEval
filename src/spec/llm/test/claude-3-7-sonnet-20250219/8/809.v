Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [-2%Z; 0%Z; 2%Z; 5%Z; 7%Z; 8%Z; 8%Z; -3%Z; -5%Z; -5%Z; 8%Z] 23%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: -2 + 0 = -2, -2 + 2 = 0, 0 + 5 = 5, 5 + 7 = 12, 12 + 8 = 20,
       20 + 8 = 28, 28 + (-3) = 25, 25 + (-5) = 20, 20 + (-5) = 15, 15 + 8 = 23 *)
    reflexivity.
  - simpl.
    (* Calculate product: -2 * 0 = 0, once zero is multiplied, product is 0 *)
    reflexivity.
Qed.