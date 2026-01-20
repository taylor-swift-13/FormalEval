Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    60 2.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum all 1's except one 2 *)
    (* count 59 ones and 1 two: sum = 59*1 + 2 = 61, but original claim is 60 *)
    (* The sum must be 60, so recount elements *)
    (* Let's count how many elements in the list: *)
    (* The list length is 59 elements in total *)
    (* So presumably the 22nd element is 2, others are 1 *)
    (* sum = 59*1 with one element as 2 means sum = (59-1)*1 + 2 = 58 + 2 = 60 *)
    reflexivity.
  - simpl.
    (* product: 1 *1*...*2*...*1 = 2 *)
    reflexivity.
Qed.