Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

(* Specification definition adapted for Real numbers *)
Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)).

(* Test case: 
   input = [1; -4; 0; 2.5; 6.8; 9; 10.2; 1.5; -4; 10.2; 10.2]
   output = [-4; 0; 7.5; 27.2; 45; 61.2; 10.5; -32; 91.8; 102]
*)
Example test_derivative : derivative_spec 
  [1; -4; 0; 2.5; 6.8; 9; 10.2; 1.5; -4; 10.2; 10.2] 
  [-4; 0; 7.5; 27.2; 45; 61.2; 10.5; -32; 91.8; 102].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (apply f_equal2; [lra | ]).
  reflexivity.
Qed.