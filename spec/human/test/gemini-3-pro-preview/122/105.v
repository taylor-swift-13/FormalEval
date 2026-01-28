Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Helper function to check if an integer has at most two digits. *)
Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

(* Precondition: 1 <= length arr <= 100 and 1 <= k <= length arr *)
Definition problem_122_pre (arr : list Z) (k : nat) : Prop :=
  (length arr >= 1)%nat /\ (length arr <= 100)%nat /\ (1 <= k)%nat /\ (k <= length arr)%nat.

(* Specification definition *)
Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

(* Test case verification *)
Example test_case_new : problem_122_spec [9; 10; 11; 100; 12; 200] 4%nat 30.
Proof.
  (* Unfold the specification definition *)
  unfold problem_122_spec.
  
  (* Simplify the expression. 
     firstn 4 [...] reduces to [9; 10; 11; 100].
     filter checks is_at_most_two_digits: 
     9 -> true, 10 -> true, 11 -> true, 100 -> false.
     Resulting list: [9; 10; 11].
     fold_left sums them: 0 + 9 + 10 + 11 = 30. *)
  simpl.
  
  (* Verify that 30 = 30 *)
  reflexivity.
Qed.