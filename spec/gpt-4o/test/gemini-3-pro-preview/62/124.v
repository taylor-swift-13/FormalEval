Require Import List.
Require Import Nat.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1%nat (length xs - 1)%nat).

Example test_derivative : derivative_spec [1; -4; 0; 2.5; 6.8; 9; 10.2; -4; -4] [-4; 0; 7.5; 27.2; 45; 61.2; -28; -32].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (apply f_equal2; [ lra | ]).
  reflexivity.
Qed.