Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; -6; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 3; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 4; 1; 1; 1; 1; 1]
    57
    (-72).
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* Compute the sum explicitly *)
    (* sum = 57 *)
    reflexivity.
  - (* product *)
    simpl.
    (* Compute the product explicitly *)
    (* product = -72 *)
    reflexivity.
Qed.