Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [-1.25; -0.75; -2.25; -1; -2; -3; -4; -5; -6; 0] [].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct (Rgt_dec _ _); try lra).
  reflexivity.
Qed.