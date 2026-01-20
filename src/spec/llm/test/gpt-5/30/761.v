Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [0; - (5 / 4); - (3 / 2); - (9 / 4); -1; -6; -4; -3; -4; -5; -6; -3; -4] [].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 0 0) as [H0|H0]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (- (5 / 4)) 0) as [H1|H1]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (- (3 / 2)) 0) as [H2|H2]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (- (9 / 4)) 0) as [H3|H3]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-1) 0) as [H4|H4]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-6) 0) as [H5|H5]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-4) 0) as [H6|H6]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-3) 0) as [H7|H7]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-4) 0) as [H8|H8]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-5) 0) as [H9|H9]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-6) 0) as [H10|H10]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-3) 0) as [H11|H11]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-4) 0) as [H12|H12]; [exfalso; lra|].
  simpl.
  reflexivity.
Qed.