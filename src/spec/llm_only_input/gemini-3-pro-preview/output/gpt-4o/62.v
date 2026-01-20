Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example test_derivative: derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  (* Unfold the definition of the specification *)
  unfold derivative_spec.
  
  (* Simplify the expression. 
     1. length [3; 1; 2; 4; 5] evaluates to 5.
     2. 5 - 1 evaluates to 4.
     3. seq 1 4 evaluates to [1; 2; 3; 4].
     4. map applies the function:
        - i=1: nth 1 xs 0 * 1 = 1 * 1 = 1
        - i=2: nth 2 xs 0 * 2 = 2 * 2 = 4
        - i=3: nth 3 xs 0 * 3 = 4 * 3 = 12
        - i=4: nth 4 xs 0 * 4 = 5 * 4 = 20
  *)
  simpl.
  
  (* The left side [1; 4; 12; 20] is now identical to the simplified right side *)
  reflexivity.
Qed.