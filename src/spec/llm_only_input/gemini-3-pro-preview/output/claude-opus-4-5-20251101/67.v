Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Psatz. (* Required for the lia tactic *)

Open Scope Z_scope.

(* Specification definition provided in the prompt *)
Definition fruit_distribution_spec (apples : Z) (oranges : Z) (n : Z) (result : Z) : Prop :=
  apples >= 0 /\
  oranges >= 0 /\
  n >= 0 /\
  n - apples - oranges >= 0 /\
  result = n - apples - oranges.

(* 
   Test case:
   Input: "5 apples and 6 oranges", n = 19
   Parsed values: apples = 5, oranges = 6, n = 19
   Expected Output: result = 8
*)

Example test_fruit_distribution : fruit_distribution_spec 5 6 19 8.
Proof.
  (* Unfold the specification to expose the logical conditions *)
  unfold fruit_distribution_spec.
  
  (* 
     The goal becomes:
     5 >= 0 /\ 6 >= 0 /\ 19 >= 0 /\ 19 - 5 - 6 >= 0 /\ 8 = 19 - 5 - 6
     
     This involves basic linear integer arithmetic.
     The 'lia' tactic (Linear Integer Arithmetic) can solve this automatically.
  *)
  lia.
Qed.