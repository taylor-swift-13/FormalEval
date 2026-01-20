Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case :
  sum_product_spec [0; 0; 0; 0; 0; 1; 1; -74; -1; -3; 0; 0; 0; 0; 0; 0] (-76) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum explicitly *)
    (* 0+0+0+0+0+1+1-74-1-3+0+0+0+0+0+0 = (1+1) + (-74-1-3) = 2 + (-78) = -76 *)
    reflexivity.
  - simpl.
    (* Compute product explicitly *)
    (* The presence of 0 anywhere makes the product 0 *)
    reflexivity.
Qed.