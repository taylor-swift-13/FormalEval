Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Example test_get_positive : get_positive_spec [9.9; -2.4785868920126473; 9.9] [9.9; 9.9].
Proof.
  unfold get_positive_spec, is_pos.
  simpl.
  destruct (Rgt_dec 9.9 0); try lra.
  destruct (Rgt_dec (-2.4785868920126473) 0); try lra.
  destruct (Rgt_dec 9.9 0); try lra.
  reflexivity.
Qed.