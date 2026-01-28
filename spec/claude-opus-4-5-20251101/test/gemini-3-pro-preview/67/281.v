Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition fruit_distribution_spec (apples : Z) (oranges : Z) (n : Z) (result : Z) : Prop :=
  apples >= 0 /\
  oranges >= 0 /\
  n >= 0 /\
  n - apples - oranges >= 0 /\
  result = n - apples - oranges.

Example fruit_distribution_test_case : fruit_distribution_spec 10 5 202 187.
Proof.
  (* Unfold the specification to see the requirements *)
  unfold fruit_distribution_spec.
  
  (* 
     The specification consists of a conjunction of 5 conditions.
     We use 'repeat split' to break them into individual subgoals
     and '; lia' to solve each linear integer arithmetic goal immediately.
     This avoids the "Wrong bullet" error by not relying on a fixed number of bullets.
  *)
  repeat split; lia.
Qed.