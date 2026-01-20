Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Definition zlist_to_natlist (l : list Z) : list nat :=
  map Z.to_nat l.

Example test_sum_product_specific_list :
  sum_product_spec (zlist_to_natlist [6%Z; 7%Z; 1%Z; 0%Z; 4%Z; 3%Z; 4%Z; 7%Z; 2%Z; 7%Z]) 41 0.
Proof.
  unfold sum_product_spec, zlist_to_natlist.
  split.
  - simpl.
    (* Evaluate the sum *)
    reflexivity.
  - simpl.
    (* Evaluate the product *)
    reflexivity.
Qed.