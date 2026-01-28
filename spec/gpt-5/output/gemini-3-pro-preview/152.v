Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition compare_spec (game guess out : list Z) : Prop :=
  List.length game = List.length guess /\
  out = List.map (fun p => match p with (a, b) => Z.abs (Z.sub a b) end) (List.combine game guess).

Example test_compare_spec :
  compare_spec 
    [1; 2; 3; 4; 5; 1] 
    [1; 2; 3; 4; 2; -2] 
    [0; 0; 0; 0; 3; 3].
Proof.
  (* Unfold the definition of the specification *)
  unfold compare_spec.
  
  (* Split the conjunction into two subgoals: length check and value check *)
  split.
  
  - (* Subgoal 1: Check if lengths are equal *)
    simpl. (* Reduces length calculations *)
    reflexivity.
    
  - (* Subgoal 2: Check if output matches the mapped calculation *)
    simpl. (* Computes combine, map, Z.sub, and Z.abs for the concrete lists *)
    reflexivity.
Qed.