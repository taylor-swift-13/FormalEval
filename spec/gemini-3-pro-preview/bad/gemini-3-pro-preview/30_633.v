Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [-89.04346588476734%R; 32.97170491287429%R; -2.25%R] [32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  destruct (Rgt_dec (-89.04346588476734) 0); [ lra | ].
  destruct (Rgt_dec 32.97170491287429 0); [ | lra ].
  destruct (Rgt_dec (-2.25) 0); [ lra | ].
  reflexivity.
Qed.