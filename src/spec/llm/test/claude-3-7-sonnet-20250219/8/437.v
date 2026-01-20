Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case :
  sum_product_spec [2%Z; 2%Z; -4%Z; 3%Z; -5%Z; 3%Z; 0%Z; -3%Z; 10%Z; 3%Z] 11 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 2+2-4+3-5+3+0-3+10+3 = 11 *)
    reflexivity.
  - simpl.
    (* Compute product: 2*2*(-4)*3*(-5)*3*0*(-3)*10*3 = 0 *)
    reflexivity.
Qed.