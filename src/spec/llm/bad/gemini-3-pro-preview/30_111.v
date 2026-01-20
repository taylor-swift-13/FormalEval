Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec [0.5; 0; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5] [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  destruct (Rgt_dec 0.5 0); try lra.
  destruct (Rgt_dec 0 0); try lra.
  destruct (Rgt_dec (-4) 0); try lra.
  destruct (Rgt_dec 2.5 0); try lra.
  destruct (Rgt_dec 5 0); try lra.
  destruct (Rgt_dec (-2.2) 0); try lra.
  destruct (Rgt_dec (-8) 0); try lra.
  destruct (Rgt_dec 7.7 0); try lra.
  destruct (Rgt_dec 9.9 0); try lra.
  destruct (Rgt_dec (-10.5) 0); try lra.
  reflexivity.
Qed.