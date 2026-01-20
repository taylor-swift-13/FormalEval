Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Adapted specification to handle list of Z rather than nat *)
Definition sum_product_spec_Z (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec_Z
    [1; 1; 1; 1; 1; -5; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    55 0.
Proof.
  unfold sum_product_spec_Z.
  split.
  - (* sum = 55 *)
    (* Compute sum explicitly: sum up all elements *)
    (* Count the number of 1's, -5, and 0's *)
    (* There are 63 elements in total (count them carefully): *)
    (* Positions with 0: positions 33 and 46 (0-based indexing assumed) *)
    (* One element is -5 at position 5 *)
    (* Rest are 1's *)
    
    (* Number of 1's = 63 - 1 (-5) - 2 zeros = 60 *)
    (* Sum = 60*1 + (-5) + 0 + 0 = 60 - 5 = 55 *)
    
    simpl.
    reflexivity.
  - (* product = 0 *)
    (* product is zero because fold includes zeros *)
    simpl.
    reflexivity.
Qed.