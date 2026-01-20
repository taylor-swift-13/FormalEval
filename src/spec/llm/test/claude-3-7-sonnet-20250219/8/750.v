Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec
    [1; 1; 1; 1; 1; -5; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    53 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate the sum explicitly *)
    (* The list sum is 53 *)
    reflexivity.
  - simpl.
    (* The product contains zero, so product is 0 *)
    reflexivity.
Qed.