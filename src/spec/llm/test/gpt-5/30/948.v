Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0%R; 10.538283343362641%R; -1.25%R; -1.5%R; -0.75%R; -2.25%R; -1%R; -2%R; 2%R; -4%R; -4%R; -5%R; -6%R]
    [10.538283343362641%R; 2%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 0%R 0%R) as [H0|H0]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec 10.538283343362641%R 0%R) as [H1|H1]; [|exfalso; lra].
  simpl.
  destruct (Rgt_dec (-1.25%R) 0%R) as [H2|H2]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-1.5%R) 0%R) as [H3|H3]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-0.75%R) 0%R) as [H4|H4]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-2.25%R) 0%R) as [H5|H5]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-1%R) 0%R) as [H6|H6]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-2%R) 0%R) as [H7|H7]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec 2%R 0%R) as [H8|H8]; [|exfalso; lra].
  simpl.
  destruct (Rgt_dec (-4%R) 0%R) as [H9|H9]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-4%R) 0%R) as [H10|H10]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-5%R) 0%R) as [H11|H11]; [exfalso; lra|].
  simpl.
  destruct (Rgt_dec (-6%R) 0%R) as [H12|H12]; [exfalso; lra|].
  simpl.
  reflexivity.
Qed.