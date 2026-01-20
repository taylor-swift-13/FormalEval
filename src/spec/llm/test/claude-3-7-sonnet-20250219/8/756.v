Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [6; 30; 0; 4; 3; 2] 45 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Nat.add [6;30;0;4;3;2] 0 = ((((0+6)+30)+0)+4)+3)+2 = 45 *)
    reflexivity.
  - simpl.
    (* fold_left Nat.mul [6;30;0;4;3;2] 1 = (((((1*6)*30)*0)*4)*3)*2 = 0 *)
    reflexivity.
Qed.