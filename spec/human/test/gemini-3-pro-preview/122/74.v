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
Example test_case_1 : problem_122_spec [100; 35; 199; 400; 500; 600; 300] 2%nat 35.
Proof.
  (* Unfold the specification definition *)
  unfold problem_122_spec.
  
  (* Simplify the expression. 
     firstn 2 [...] reduces to [100; 35].
     filter checks is_at_most_two_digits: 
       100 is not < 100 (false).
       35 is < 100 and > -100 (true).
     fold_left sums [35]: 0 + 35 = 35. *)
  simpl.
  
  (* Verify that 35 = 35 *)
  reflexivity.
Qed.