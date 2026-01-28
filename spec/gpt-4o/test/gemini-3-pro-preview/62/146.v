Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [1; -4; 0; -4.5; 6.8; 9; 6.8] [-4; 0; -13.5; 27.2; 45; 40.8].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (apply f_equal2; [ lra | ]).
  reflexivity.
Qed.