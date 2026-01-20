Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_spec :
  sum_product_spec [0%Z; 9%Z; 1%Z; 10%Z; 19%Z; 0%Z; 8%Z; 10%Z; (-10)%Z] 47 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate the sum manually: 0+9+1+10+19+0+8+10+(-10) = 47 *)
    reflexivity.
  - simpl.
    (* Calculate the product manually: 0 * ... = 0 *)
    reflexivity.
Qed.