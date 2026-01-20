Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition compare_spec (game guess out : list Z) : Prop :=
  List.length game = List.length guess /\
  out = List.map (fun p => match p with (a, b) => Z.abs (Z.sub a b) end) (List.combine game guess).

Example test_compare_spec: 
  compare_spec [1; 2; 3; 4; 5; 1] [1; 2; 3; 4; 2; -2] [0; 0; 0; 0; 3; 3].
Proof.
  (* Unfold the definition of the specification *)
  unfold compare_spec.
  
  (* Split the conjunction into two subgoals: length equality and content equality *)
  split.
  
  - (* Subgoal 1: Prove lengths are equal *)
    simpl. (* Simplify the length calculation *)
    reflexivity. (* Check for equality *)
    
  - (* Subgoal 2: Prove the output list matches the calculation *)
    simpl. (* Perform the map, combine, sub, and abs computations *)
    reflexivity. (* Check that the computed list equals the expected output *)
Qed.