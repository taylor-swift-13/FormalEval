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
Example test_case_1 : problem_122_spec [111; 3; 321; 500; 21; 300; 600; 222; 600] 3%nat 3.
Proof.
  (* Unfold the specification definition *)
  unfold problem_122_spec.
  
  (* Simplify the expression. 
     firstn 3 [...] reduces to [111; 3; 321].
     filter checks is_at_most_two_digits: 
       111 is false (-100 < 111 < 100 is false),
       3 is true,
       321 is false.
     filtered list is [3].
     fold_left sums them: 0 + 3 = 3. *)
  simpl.
  
  (* Verify that 3 = 3 *)
  reflexivity.
Qed.