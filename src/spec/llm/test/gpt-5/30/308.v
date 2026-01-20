Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [IZR 0%Z; 7.7%R; (-1.5)%R; (-0.75)%R; (-2.25)%R; IZR (-1)%Z; IZR (-2)%Z; IZR (-4)%Z; IZR (-5)%Z; IZR (-3)%Z; (-2.25)%R; IZR 0%Z; (-0.75)%R] [7.7%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (IZR 0%Z)) as [H0|H0]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 7.7%R) as [H1|H1]; [|exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-1.5)%R) as [H2|H2]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (-0.75)%R) as [H3|H3]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (-2.25)%R) as [H4|H4]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR (-1)%Z)) as [H5|H5]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR (-2)%Z)) as [H6|H6]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR (-4)%Z)) as [H7|H7]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR (-5)%Z)) as [H8|H8]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR (-3)%Z)) as [H9|H9]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (-2.25)%R) as [H10|H10]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (IZR 0%Z)) as [H11|H11]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (-0.75)%R) as [H12|H12]; [exfalso; lra|].
  simpl.
  reflexivity.
Qed.