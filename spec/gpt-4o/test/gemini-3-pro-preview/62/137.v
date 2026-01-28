Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1%nat (length xs - 1)%nat).

Example test_derivative : derivative_spec [1; -5; -4; 0; 2.5; 6.8; 9; 3.5] [-5; -8; 0; 10; 34; 54; 24.5].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.