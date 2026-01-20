Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0%R x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [-1.25%R; -0.75%R; -2.25%R; -1%R; -2%R; -3%R; -4%R; -5%R; -6%R; 0%R] [].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0%R (-1.25%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-0.75%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-2.25%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-1%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-2%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-3%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-4%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-5%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (-6%R)); [lra|].
  simpl.
  destruct (Rlt_dec 0%R (0%R)); [lra|].
  simpl.
  reflexivity.
Qed.