Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec 
  [1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; 0] 
  [3.5; -5.6; 3.3; -17.6; -22.5; -30; 24.5; 0].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (apply f_equal2; [ lra | ]); reflexivity.
Qed.