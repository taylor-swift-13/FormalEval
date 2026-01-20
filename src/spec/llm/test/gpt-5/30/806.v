Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; 2.5%R; IZR 5; (-2.2)%R; (-2.651030586877352)%R; IZR (-8); 7.7%R; 9.9%R; (-10.5)%R; 9.9%R]
    [0.5%R; 2.5%R; IZR 5; 7.7%R; 9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 0.5 0) as [H1|H1]; [| exfalso; apply H1; lra].
  simpl.
  destruct (Rgt_dec 2.5 0) as [H2|H2]; [| exfalso; apply H2; lra].
  simpl.
  destruct (Rgt_dec (IZR 5) 0) as [H3|H3]; [| exfalso; apply H3; lra].
  simpl.
  destruct (Rgt_dec (-2.2) 0) as [H4|H4]; [exfalso; apply (Rgt_not_le _ _ H4); lra |].
  simpl.
  destruct (Rgt_dec (-2.651030586877352) 0) as [H5|H5]; [exfalso; apply (Rgt_not_le _ _ H5); lra |].
  simpl.
  destruct (Rgt_dec (IZR (-8)) 0) as [H6|H6]; [exfalso; apply (Rgt_not_le _ _ H6); lra |].
  simpl.
  destruct (Rgt_dec 7.7 0) as [H7|H7]; [| exfalso; apply H7; lra].
  simpl.
  destruct (Rgt_dec 9.9 0) as [H8|H8]; [| exfalso; apply H8; lra].
  simpl.
  destruct (Rgt_dec (-10.5) 0) as [H9|H9]; [exfalso; apply (Rgt_not_le _ _ H9); lra |].
  simpl.
  destruct (Rgt_dec 9.9 0) as [H10|H10]; [| exfalso; apply H10; lra].
  simpl.
  reflexivity.
Qed.