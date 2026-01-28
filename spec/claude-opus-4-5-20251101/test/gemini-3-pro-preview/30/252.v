Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -11.18889279027017; -8; -4; -7; 9.9; -11.18889279027017; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct Rgt_dec; try lra).
  reflexivity.
Qed.