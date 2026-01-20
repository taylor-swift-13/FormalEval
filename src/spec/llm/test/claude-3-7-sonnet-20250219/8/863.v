Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; -2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; -6%Z; -6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 
     1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 5%Z]
    51 8640.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    (* Use fold_left with Z.add on the list *)
    (* Compute to verify *)
    reflexivity.
  - (* product *)
    (* Use fold_left with Z.mul on the list *)
    reflexivity.
Qed.