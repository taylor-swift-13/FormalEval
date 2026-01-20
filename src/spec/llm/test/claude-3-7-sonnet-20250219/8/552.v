Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -7%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z]
    55 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum manually: in the list, all ones except one -7, one 4, one 0. *)
    (* Sum of ones: count how many 1's *)
    (* There are 58 elements total *)
    (* Elements: 58 total elements:
         7 ones,
         then -7,
         then 23 ones,
         then 4,
         then 14 ones,
         then 0,
         then 2 ones.
       Total: 7 + 1 + 23 + 1 + 14 + 1 + 2 = 49, recount carefully:
       Actually: 
         The list is:
         [1;1;1;1;1;1;1; -7; 1;1;1;1;1;1;1;1;
          1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;
          1;1;1;1;4;1;1;1;1;1;1;1;1;1;1;1;
          1;1;1;1;1;1;1;1;1;0;1;1]
       Counting ones:
         first block: 7 ones
         then -7
         second block: 8 ones (positions 9-16)
         third block: 14 ones (positions 17-30)
         then 4
         then 14 ones (positions 32-45)
         then 0
         then 2 ones (positions 47-48)
       Let's count precisely:
       7 + 8 + 14 + 14 + 2 = 45 ones
       Wait, another recount:
       From list:
       Positions:
       1-7 -> ones (7)
       8 -> -7
       9-16 -> ones (8)
       17-30 -> ones (14)
       31 -> 4
       32-45 -> ones (14)
       46 -> 0
       47-48 -> ones (2)
       Total ones = 7 + 8 + 14 + 14 + 2 = 45 ones
       Sum = 45*1 + (-7) + 4 + 0 = 45 -7 +4 +0 = 42 *)
    reflexivity.
  - simpl.
    (* Product: since the list contains a 0, the product is 0 *)
    reflexivity.
Qed.