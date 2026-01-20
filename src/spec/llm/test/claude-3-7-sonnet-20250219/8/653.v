Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product :
  sum_product_spec [1; 2; 4; -3; 0; -3; 8] 9 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step by step: 0+1=1, 1+2=3, 3+4=7, 7+(-3)=4, 4+0=4, 4+(-3)=1, 1+8=9 *)
    reflexivity.
  - simpl.
    (* Compute product step by step: 1*1=1, 1*2=2, 2*4=8, 8*(-3)=-24, -24*0=0, 0*(-3)=0, 0*8=0 *)
    reflexivity.
Qed.