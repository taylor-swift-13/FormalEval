Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [9.9%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R; 25.12472520208241%R; -2.25%R]
    [9.9%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R; 25.12472520208241%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (Hpos1 : 0 < 9.9%R) by lra.
  assert (Hpos2 : 0 < 25.12472520208241%R) by lra.
  assert (Hpos3 : 0 < 33.195768044846155%R) by lra.
  assert (Hneg : ~ 0 < -2.25%R) by lra.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1]; [|exfalso; apply H1; exact Hpos1].
  simpl.
  destruct (Rlt_dec 0 25.12472520208241%R) as [H2|H2]; [|exfalso; apply H2; exact Hpos2].
  simpl.
  destruct (Rlt_dec 0 33.195768044846155%R) as [H3|H3]; [|exfalso; apply H3; exact Hpos3].
  simpl.
  destruct (Rlt_dec 0 (-2.25%R)) as [H4|H4]; [exfalso; apply Hneg; exact H4 |].
  simpl.
  destruct (Rlt_dec 0 33.195768044846155%R) as [H5|H5]; [|exfalso; apply H5; exact Hpos3].
  simpl.
  destruct (Rlt_dec 0 25.12472520208241%R) as [H6|H6]; [|exfalso; apply H6; exact Hpos2].
  simpl.
  destruct (Rlt_dec 0 (-2.25%R)) as [H7|H7]; [exfalso; apply Hneg; exact H7 |].
  simpl.
  reflexivity.
Qed.