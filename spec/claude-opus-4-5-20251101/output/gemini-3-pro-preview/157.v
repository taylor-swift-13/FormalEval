Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_3_4_5 : right_angle_triangle_spec 3 4 5 true.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: true = true -> (3*3 + 4*4 = 5*5 \/ ...) *)
    intros _.
    (* The first condition (a^2 + b^2 = c^2) holds for 3, 4, 5 *)
    left.
    (* Verify 3*3 + 4*4 = 5*5 *)
    simpl.
    reflexivity.
    
  - (* Subgoal 2: (3*3 + 4*4 = 5*5 \/ ...) -> true = true *)
    intros _.
    reflexivity.
Qed.