Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; -1%Z; -3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-3) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add sums the list *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul multiplies all elements; presence of 0 yields product 0 *)
    reflexivity.
Qed.