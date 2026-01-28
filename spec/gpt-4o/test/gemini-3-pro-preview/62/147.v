Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1%nat (length xs - 1%nat)).

Example test_derivative : derivative_spec [3.5; -2.8; 1.1; -4.4; -5; 3.5; 0] [-2.8; 2.2; -13.2; -20; 17.5; 0].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.