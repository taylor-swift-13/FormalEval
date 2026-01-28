Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [if Rgt_dec ?x 0 then _ else _] =>
      destruct (Rgt_dec x 0); [ try lra | try lra ]
  end.
  reflexivity.
Qed.