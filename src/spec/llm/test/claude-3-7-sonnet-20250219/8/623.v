Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [6%Z; 1%Z; 0%Z; 4%Z; 3%Z; 7%Z; 2%Z] 23%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. (* fold_left Z.add over the list [6;1;0;4;3;7;2] starting at 0 *)
    reflexivity.
  - simpl. (* fold_left Z.mul over the list [6;1;0;4;3;7;2] starting at 1 *)
    reflexivity.
Qed.