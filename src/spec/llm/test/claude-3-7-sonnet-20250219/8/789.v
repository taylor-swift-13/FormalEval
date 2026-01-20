Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_long_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; -6; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 3; -8; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    49
    144.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum of the list *)
    reflexivity.
  - simpl.
    (* product of the list *)
    reflexivity.
Qed.