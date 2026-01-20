Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-9) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Sum: 0+0+0+0+0+(-6)+1+(-1)+(-3)+0+0+0+0+0+0+0 = -9 *)
    reflexivity.
  - simpl.
    (* Product: all multiplied, contains 0, so product is 0 *)
    reflexivity.
Qed.