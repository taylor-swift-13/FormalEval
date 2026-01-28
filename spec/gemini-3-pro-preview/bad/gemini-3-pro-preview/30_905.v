Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : get_positive_spec [-89.04346588476734; -2.6958053769612267] [].
Proof.
  unfold get_positive_spec.
  unfold Rgt_bool.
  simpl.
  destruct (Rgt_dec (-89.04346588476734) 0); try lra.
  destruct (Rgt_dec (-2.6958053769612267) 0); try lra.
  reflexivity.
Qed.