Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [2; 4; 8; 16; 16; 4; 16; 16; 5; (-1); 2; 4; 16; 4; 4; 2] 118 (-343597383680).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 2+4=6, +8=14, +16=30, +16=46, +4=50, +16=66, +16=82, +5=87, +(-1)=86, +2=88, +4=92, +16=108, +4=112, +4=116, +2=118 *)
    reflexivity.
  - simpl.
    (* Compute product:
       2 * 4 = 8
       8 * 8 = 64
       64 * 16 = 1024
       1024 * 16 = 16384
       16384 * 4 = 65536
       65536 * 16 = 1048576
       1048576 * 16 = 16777216
       16777216 * 5 = 83886080
       83886080 * (-1) = -83886080
       -83886080 * 2 = -167772160
       -167772160 * 4 = -671088640
       -671088640 * 16 = -10737418240
       -10737418240 * 4 = -42949672960
       -42949672960 * 4 = -171798691840
       -171798691840 * 2 = -343597383680
    *)
    reflexivity.
Qed.