Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [3.5; -2.8; 1.1; -4.4; 0] [-2.8; 2.2; -13.2; 0].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.