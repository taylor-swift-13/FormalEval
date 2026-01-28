Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 0; 0; 0; 0; 10], output = [0; 0; 0; 0; 50] *)
(* Note: The input uses nat literals to match the type signature (list nat) of the specification *)
Example test_derivative : derivative_spec [0; 0; 0; 0; 0; 10] [0; 0; 0; 0; 50].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [0; 0; 0; 0; 0; 10] reduces to 6.
     2. seq 1 (6 - 1) reduces to [1; 2; 3; 4; 5].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 0 * 1 = 0
        - i=2: nth 2 xs 0 * 2 = 0 * 2 = 0
        - i=3: nth 3 xs 0 * 3 = 0 * 3 = 0
        - i=4: nth 4 xs 0 * 4 = 0 * 4 = 0
        - i=5: nth 5 xs 0 * 5 = 10 * 5 = 50
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.