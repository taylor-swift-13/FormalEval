Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [5%Z; 1%Z; 3%Z; -10%Z; 3%Z; 4%Z; 3%Z; 7%Z; 2%Z] 18 (-75600).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum *)
    reflexivity.
  - simpl.
    (* Compute the product *)
    reflexivity.
Qed.