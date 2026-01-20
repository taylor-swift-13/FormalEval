Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_list :
  sum_product_spec [-6%Z; 2%Z; 4%Z; -6%Z; 0%Z; 8%Z; -10%Z; -6%Z] (-14) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum step by step *)
    (* fold_left Z.add [-6;2;4;-6;0;8;-10;-6] 0 = (((((((0 + -6) + 2) + 4) + -6) + 0) + 8) + -10) + -6 *)
    reflexivity.
  - simpl.
    (* Calculate product step by step *)
    (* fold_left Z.mul [...] 1 = 0 because multiplication by 0 *)
    reflexivity.
Qed.