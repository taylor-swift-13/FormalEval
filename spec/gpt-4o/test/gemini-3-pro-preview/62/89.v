Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [7; 2], output = [2] *)
(* Note: The input uses nat literals to match the type signature (list nat) of the specification *)
Example test_derivative : derivative_spec [7; 2] [2].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [7; 2] reduces to 2.
     2. seq 1 (2 - 1) reduces to [1].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 2 * 1 = 2
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.