Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [1; 4; -3; 0; 8; 1; 0] 11 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* compute sum: 1+4=5, 5-3=2, 2+0=2, 2+8=10, 10+1=11, 11+0=11 *)
    reflexivity.
  - simpl.
    (* compute product: 1*4=4, 4*(-3)=-12, -12*0=0, 0*8=0, 0*1=0, 0*0=0 *)
    reflexivity.
Qed.