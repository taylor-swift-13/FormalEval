Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_5_12_13 : right_angle_triangle_spec 5 12 13 true.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: true = true -> (5*5 + 12*12 = 13*13 \/ ...) *)
    intros _.
    (* The first condition (a^2 + b^2 = c^2) holds for 5, 12, 13 *)
    left.
    (* Verify 5*5 + 12*12 = 13*13 *)
    simpl.
    reflexivity.
    
  - (* Subgoal 2: (5*5 + 12*12 = 13*13 \/ ...) -> true = true *)
    intros _.
    reflexivity.
Qed.