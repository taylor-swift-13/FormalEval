Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_35_138_138 : right_angle_triangle_spec 35 138 138 false.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: false = true -> ... *)
    intros H.
    (* This premise is contradictory *)
    discriminate H.
    
  - (* Subgoal 2: (...) -> false = true *)
    intros H.
    (* Simplify the arithmetic expressions in the hypothesis *)
    simpl in H.
    (* LIA (Linear Integer Arithmetic) can solve the contradictions arising from the equations *)
    lia.
Qed.