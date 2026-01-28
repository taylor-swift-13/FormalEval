Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Fixpoint filter_pos (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: filter_pos xs else filter_pos xs
  end.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter_pos l.

Example test_get_positive:
  get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; 9.9; -11.18889279027017; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (match goal with |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); [ try lra | try lra ] end).
  reflexivity.
Qed.