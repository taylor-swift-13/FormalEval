Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [-6%Z; 1%Z; -4%Z; 7%Z; 4%Z; -6%Z; 8%Z; -11%Z; -5%Z; 8%Z; 0%Z; -4%Z] (-8) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum manually: 
       -6 + 1 = -5
       -5 + -4 = -9
       -9 + 7 = -2
       -2 + 4 = 2
       2 + -6 = -4
       -4 + 8 = 4
       4 + -11 = -7
       -7 + -5 = -12
       -12 + 8 = -4
       -4 + 0 = -4
       -4 + -4 = -8
    *)
    reflexivity.
  - simpl.
    (* product involves 0, so product is 0 *)
    reflexivity.
Qed.