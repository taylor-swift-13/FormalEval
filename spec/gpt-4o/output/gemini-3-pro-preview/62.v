Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [3; 1; 2; 4; 5], output = [1; 4; 12; 20] *)
(* Note: The input uses nat literals to match the type signature (list nat) of the specification *)
Example test_derivative : derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [3; 1; 2; 4; 5] reduces to 5.
     2. seq 1 (5 - 1) reduces to [1; 2; 3; 4].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 1 * 1 = 1
        - i=2: nth 2 xs 0 * 2 = 2 * 2 = 4
        - i=3: nth 3 xs 0 * 3 = 4 * 3 = 12
        - i=4: nth 4 xs 0 * 4 = 5 * 4 = 20
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.