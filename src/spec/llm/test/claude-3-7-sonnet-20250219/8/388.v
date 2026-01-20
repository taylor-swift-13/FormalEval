Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [2%Z; 20%Z; -7%Z; 0%Z; 1%Z; 0%Z; 0%Z] 16 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 2 + 20 = 22, 22 + (-7) = 15, 15 + 0 = 15, 15 + 1 = 16, 16 + 0 = 16, 16 + 0 = 16 *)
    reflexivity.
  - simpl.
    (* Compute product: 1*2 = 2, 2*20 = 40, 40*(-7) = -280, -280*0 = 0, 0*1 = 0, 0*0 = 0, 0*0 = 0 *)
    reflexivity.
Qed.