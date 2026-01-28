Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_13_120_120 : right_angle_triangle_spec 13 120 120 false.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: false = true -> ... *)
    intros H.
    (* The premise false = true is a contradiction *)
    inversion H.
    
  - (* Subgoal 2: (... \/ ...) -> false = true *)
    intros [H | [H | H]].
    (* Case 1: 13*13 + 120*120 = 120*120 *)
    + simpl in H. discriminate.
    (* Case 2: 13*13 + 120*120 = 120*120 *)
    + simpl in H. discriminate.
    (* Case 3: 120*120 + 120*120 = 13*13 *)
    + simpl in H. discriminate.
Qed.