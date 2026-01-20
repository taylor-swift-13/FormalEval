Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [-2.651030586877352; -4; 2.5; 5; -2.651030586877352; -8; 8.193677988449515; 7.7; 9.9; -10.5; 9.9; -2.2]
    [2.5; 5; 8.193677988449515; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (-2.651030586877352)) as [H1|H1]; [lra|].
  simpl.
  destruct (Rlt_dec 0 (-4)) as [H2|H2]; [lra|].
  simpl.
  destruct (Rlt_dec 0 2.5) as [H3|H3]; [|lra].
  simpl.
  destruct (Rlt_dec 0 5) as [H4|H4]; [|lra].
  simpl.
  destruct (Rlt_dec 0 (-2.651030586877352)) as [H5|H5]; [lra|].
  simpl.
  destruct (Rlt_dec 0 (-8)) as [H6|H6]; [lra|].
  simpl.
  destruct (Rlt_dec 0 8.193677988449515) as [H7|H7]; [|lra].
  simpl.
  destruct (Rlt_dec 0 7.7) as [H8|H8]; [|lra].
  simpl.
  destruct (Rlt_dec 0 9.9) as [H9|H9]; [|lra].
  simpl.
  destruct (Rlt_dec 0 (-10.5)) as [H10|H10]; [lra|].
  simpl.
  destruct (Rlt_dec 0 9.9) as [H11|H11]; [|lra].
  simpl.
  destruct (Rlt_dec 0 (-2.2)) as [H12|H12]; [lra|].
  simpl.
  reflexivity.
Qed.