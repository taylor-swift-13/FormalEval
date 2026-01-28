Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_9999_3_3 : right_angle_triangle_spec 9999 3 3 false.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: false = true -> ... *)
    intros H.
    discriminate.
    
  - (* Subgoal 2: (...) -> false = true *)
    intros [H | [H | H]]; lia.
Qed.