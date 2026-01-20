Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_sample_list :
  sum_product_spec [2%Z; 4%Z; -6%Z; 1%Z; 8%Z; -5%Z; -10%Z; 4%Z; 4%Z] 2%Z (-307200)%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum calculation: 2 + 4 = 6; 6 + (-6) = 0; 0 + 1 = 1; 1 + 8 = 9; 9 + (-5) = 4; 4 + (-10) = -6; -6 + 4 = -2; -2 + 4 = 2 *)
    reflexivity.
  - simpl.
    (* product calculation:
       1 * 2 = 2
       2 * 4 = 8
       8 * (-6) = -48
       -48 * 1 = -48
       -48 * 8 = -384
       -384 * (-5) = 1920
       1920 * (-10) = -19200
       -19200 * 4 = -76800
       -76800 * 4 = -307200
    *)
    reflexivity.
Qed.