Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case :
  sum_product_spec [0%Z; 1%Z; 10%Z; 20%Z; 0%Z; 8%Z; 10%Z; (-10)%Z] 39 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step-by-step: 0+1=1, 1+10=11, 11+20=31, 31+0=31, 31+8=39, 39+10=49, 49+(-10)=39 *)
    reflexivity.
  - simpl.
    (* Compute product step-by-step: 1*0=0, all next multiplications stay 0 *)
    reflexivity.
Qed.