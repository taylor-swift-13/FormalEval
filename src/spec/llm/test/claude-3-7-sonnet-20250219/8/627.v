Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex :
  sum_product_spec 
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     -6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    55
    (-18).
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* We can compute fold_left Z.add over this list *)
    change (fold_left Z.add 
      [1;1;1;1;1;1;1;1;1;1;
       -6;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;3;1;1;1;
       1;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;1;1;1;1] 0) with
      (fold_left Z.add 
      [1;1;1;1;1;1;1;1;1;1;
       -6;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;3;1;1;1;
       1;1;1;1;1;1;1;1;1;1;
       1;1;1;1;1;1;1;1;1;1] 0).
    (* Sum all elements: count number of 1's first *)
    (* There are 60 elements total (10 + 50 after) *)
    (* In the list: eleven 1's before -6, then many 1's, one 3 *)
    (* Let's count 1's: total 60 elements:
         - at start 10 of 1,
         - at position 11: -6,
         - from 12 to 35: 24 ones,
         - at 36: 3,
         - from 37 to 60: 24 ones
       Total ones = 10 + 24 + 24 = 58 ones
       Sum = 1*58 + (-6) + 3 = 58 - 6 + 3 = 55 *)
    reflexivity.
  - (* product *)
    simpl.
    (* Calculate product:
       Product = (1^10) * (-6) * (1^24) * 3 * (1^24)
       = (-6) * 3 = -18 *)
    reflexivity.
Qed.