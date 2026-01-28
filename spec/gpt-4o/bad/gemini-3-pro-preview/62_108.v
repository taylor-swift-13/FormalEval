Require Import List.
Require Import Reals.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  result = map (fun i => nth i xs 0 * INR i) (seq 1 (length xs - 1)%nat).

Example test_derivative : derivative_spec 
  [1.5; -2; 0; 3.14; -5; 0; 1.2; 0; -4.5; 0; 2] 
  [-2; 0; 9.42; -20; 0; 7.2; 0; -36; 0; 20].
Proof.
  unfold derivative_spec.
  simpl.
  repeat (apply f_equal2; [ field | ]).
  reflexivity.
Qed.