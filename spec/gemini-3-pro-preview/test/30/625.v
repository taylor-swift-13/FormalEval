Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : get_positive_spec [-89.04346588476734%R; 9.9%R; 32.97170491287429%R; -2.25%R] [9.9%R; 32.97170491287429%R].
Proof.
  unfold get_positive_spec, Rgt_bool.
  simpl.
  repeat (destruct (Rgt_dec _ _); try lra).
  reflexivity.
Qed.