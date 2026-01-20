Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec [-1.25; -0.75; -2.25; -1; -2; -3; -4; -5; -6; 0] [].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  repeat (destruct (Rgt_dec _ _); [ lra | ]).
  reflexivity.
Qed.