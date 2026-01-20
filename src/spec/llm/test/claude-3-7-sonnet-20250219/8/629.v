Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [6%Z; 30%Z; 0%Z; 4%Z; 3%Z; 7%Z; 2%Z] 52 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [6;30;0;4;3;7;2] 0 = 6+30+0+4+3+7+2 = 52 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [6;30;0;4;3;7;2] 1 = 6*30*0*4*3*7*2 = 0 *)
    reflexivity.
Qed.