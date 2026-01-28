Require Import List.
Require Import Reals.
Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; 9.9; -11.18889279027017; -10.5; 2.5] 
  [0.5; 2.5; 5; 9.9; 2.5].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  repeat (destruct Rgt_dec; try lra).
  reflexivity.
Qed.