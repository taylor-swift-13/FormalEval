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
Example test_case_1 : problem_122_spec [1000; 20; 300; 20; 6000; 500; 10000; 6000; 40000] 6%nat 40.
Proof.
  (* Unfold the specification definition *)
  unfold problem_122_spec.
  
  (* Simplify the expression. 
     firstn 6 [...] reduces to [1000; 20; 300; 20; 6000; 500].
     filter checks is_at_most_two_digits:
       1000 -> false
       20 -> true
       300 -> false
       20 -> true
       6000 -> false
       500 -> false
     Filtered list is [20; 20].
     fold_left sums them: 0 + 20 + 20 = 40. *)
  simpl.
  
  (* Verify that 40 = 40 *)
  reflexivity.
Qed.