Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [2%Z; 4%Z; -6%Z; -4%Z; 8%Z; -10%Z; 4%Z; 4%Z] 2 (-245760).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step: 0+2=2, 2+4=6, 6+(-6)=0, 0+(-4)=-4, -4+8=4, 4+(-10)=-6, -6+4=-2, -2+4=2 *)
    reflexivity.
  - simpl.
    (* Compute the product step by step:
       1*2=2
       2*4=8
       8*(-6)=-48
       -48*(-4)=192
       192*8=1536
       1536*(-10)=-15360
       -15360*4=-61440
       -61440*4=-245760
    *)
    reflexivity.
Qed.