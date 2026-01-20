Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [7.878953248636265%R; 7.1018462924316985%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R; 33.195768044846155%R; 33.195768044846155%R]
    [7.878953248636265%R; 7.1018462924316985%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R; 33.195768044846155%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 7.878953248636265%R 0) as [H1|H1]; simpl; [ | exfalso; apply H1; lra ].
  destruct (Rgt_dec 7.1018462924316985%R 0) as [H2|H2]; simpl; [ | exfalso; apply H2; lra ].
  destruct (Rgt_dec 25.12472520208241%R 0) as [H3|H3]; simpl; [ | exfalso; apply H3; lra ].
  destruct (Rgt_dec 33.195768044846155%R 0) as [H4|H4]; simpl; [ | exfalso; apply H4; lra ].
  destruct (Rgt_dec (-2.25%R) 0) as [H5|H5]; [ exfalso; lra | simpl ].
  destruct (Rgt_dec 33.195768044846155%R 0) as [H6|H6]; simpl; [ | exfalso; apply H6; lra ].
  destruct (Rgt_dec 33.195768044846155%R 0) as [H7|H7]; simpl; [ | exfalso; apply H7; lra ].
  destruct (Rgt_dec 33.195768044846155%R 0) as [H8|H8]; simpl; [ | exfalso; apply H8; lra ].
  reflexivity.
Qed.