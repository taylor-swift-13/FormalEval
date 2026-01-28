Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_float : 
  right_angle_triangle_spec 
    120.27264036217386 
    95.48313167066331 
    26.117120159873124 
    false.
Proof.
  (* Unfold the specification definition *)
  unfold right_angle_triangle_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Subgoal 1: false = true -> ... *)
    intros H.
    (* Contradiction: false is not true *)
    discriminate H.
    
  - (* Subgoal 2: (... \/ ... \/ ...) -> false = true *)
    intros [H | [H | H]];
    (* Use non-linear real arithmetic solver to prove contradiction *)
    nra.
Qed.