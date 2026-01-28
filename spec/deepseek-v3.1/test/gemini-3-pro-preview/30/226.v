Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example test_get_positive:
  get_positive_spec [-3; 0.5; -4; 2.5; 5; -2.2; -8; -4; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct Rlt_dec; try lra).
  reflexivity.
Qed.