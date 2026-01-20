Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    60
    2.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* Count elements: there are 59 ones and one '2', sum is 59*1 + 2 = 61 *)
    (* But actual list length is 59 elements? Let's count carefully. *)
    (* Counting elements in list: *)
    (* number of 1's before 2: 34 *)
    (* then 2 *)
    (* then rest 1's: 24 *)
    (* total 34 + 1 + 24 = 59 elements *)
    (* sum = 34*1 + 2 + 24*1 = 34 + 2 + 24 = 60 *)
    reflexivity.
  - (* product *)
    simpl.
    (* all elements are 1 except one 2: product = 1*1*...*2*...*1 = 2 *)
    reflexivity.
Qed.