Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Nat.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [3.5; -2.8; 1.1; -4.4; 0; 3.5] [-2.8; 2.2; -13.2; 0; 17.5].
Proof.
  unfold derivative_spec.
  simpl.
  repeat f_equal; try lra.
Qed.