Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 2; 0; 3; 0; 4; 5], output = [2; 0; 9; 0; 20; 30] *)
Example test_derivative : derivative_spec [0; 2; 0; 3; 0; 4; 5] [2; 0; 9; 0; 20; 30].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [0; 2; 0; 3; 0; 4; 5] reduces to 7.
     2. seq 1 (7 - 1) reduces to [1; 2; 3; 4; 5; 6].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 2 * 1 = 2
        - i=2: nth 2 xs 0 * 2 = 0 * 2 = 0
        - i=3: nth 3 xs 0 * 3 = 3 * 3 = 9
        - i=4: nth 4 xs 0 * 4 = 0 * 4 = 0
        - i=5: nth 5 xs 0 * 5 = 4 * 5 = 20
        - i=6: nth 6 xs 0 * 6 = 5 * 6 = 30
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.