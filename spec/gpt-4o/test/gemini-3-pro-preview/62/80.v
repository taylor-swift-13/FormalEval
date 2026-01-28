Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 3; 0; 1; 1; 0; 6; 0], output = [3; 0; 3; 4; 0; 36; 0] *)
(* Note: The input uses nat literals to match the type signature (list nat) of the specification *)
Example test_derivative : derivative_spec [0; 3; 0; 1; 1; 0; 6; 0] [3; 0; 3; 4; 0; 36; 0].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [0; 3; 0; 1; 1; 0; 6; 0] reduces to 8.
     2. seq 1 (8 - 1) reduces to [1; 2; 3; 4; 5; 6; 7].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 3 * 1 = 3
        - i=2: nth 2 xs 0 * 2 = 0 * 2 = 0
        - i=3: nth 3 xs 0 * 3 = 1 * 3 = 3
        - i=4: nth 4 xs 0 * 4 = 1 * 4 = 4
        - i=5: nth 5 xs 0 * 5 = 0 * 5 = 0
        - i=6: nth 6 xs 0 * 6 = 6 * 6 = 36
        - i=7: nth 7 xs 0 * 7 = 0 * 7 = 0
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.