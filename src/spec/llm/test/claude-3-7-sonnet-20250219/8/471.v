Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 21%Z; -10%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    77 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum *)
    (* The sum is:
       1+1+1+1+1+1+6+1+1+1+1+1+1+2+1+1+1+1+1+1+1+1+1+1+1+0+1+1+1+1+1+1+1+1+2+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+21+(-10)+1+1+1+1+1+1+1+1+1
       = 77
    *)
    reflexivity.
  - simpl.
    (* The product contains 0, so product is 0 *)
    reflexivity.
Qed.