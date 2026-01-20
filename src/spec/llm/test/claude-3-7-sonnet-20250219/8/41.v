Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [2; 13; 7; 11; 13; 49] 95 1275274.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.