Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [-3; 0.5; -4; 2.5; 5; -2.2; 0.3470794389448922; -8; -4; -7; 9.9; -10.5] [0.5; 2.5; 5; 0.3470794389448922; 9.9].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  destruct (Rgt_dec (-3) 0); [ lra | ].
  destruct (Rgt_dec 0.5 0); [ | lra ].
  destruct (Rgt_dec (-4) 0); [ lra | ].
  destruct (Rgt_dec 2.5 0); [ | lra ].
  destruct (Rgt_dec 5 0); [ | lra ].
  destruct (Rgt_dec (-2.2) 0); [ lra | ].
  destruct (Rgt_dec 0.3470794389448922 0); [ | lra ].
  destruct (Rgt_dec (-8) 0); [ lra | ].
  destruct (Rgt_dec (-4) 0); [ lra | ].
  destruct (Rgt_dec (-7) 0); [ lra | ].
  destruct (Rgt_dec 9.9 0); [ | lra ].
  destruct (Rgt_dec (-10.5) 0); [ lra | ].
  reflexivity.
Qed.