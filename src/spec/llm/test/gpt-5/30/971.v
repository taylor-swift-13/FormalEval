Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [21.28666897792971%R; 9.9%R; 21.859816644520016%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R; 25.12472520208241%R; 33.195768044846155%R]
    [21.28666897792971%R; 9.9%R; 21.859816644520016%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R; 25.12472520208241%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 21.28666897792971%R) as [H1|H1]; [|exfalso; apply H1; lra].
  destruct (Rlt_dec 0 9.9%R) as [H2|H2]; [|exfalso; apply H2; lra].
  destruct (Rlt_dec 0 21.859816644520016%R) as [H3|H3]; [|exfalso; apply H3; lra].
  destruct (Rlt_dec 0 25.12472520208241%R) as [H4|H4]; [|exfalso; apply H4; lra].
  destruct (Rlt_dec 0 33.195768044846155%R) as [H5|H5]; [|exfalso; apply H5; lra].
  destruct (Rlt_dec 0 (-2.25%R)) as [H6|H6].
  - assert (~ (0 < -2.25%R)) by lra. contradiction.
  - destruct (Rlt_dec 0 33.195768044846155%R) as [H7|H7]; [|exfalso; apply H7; lra].
    destruct (Rlt_dec 0 25.12472520208241%R) as [H8|H8]; [|exfalso; apply H8; lra].
    destruct (Rlt_dec 0 33.195768044846155%R) as [H9|H9]; [|exfalso; apply H9; lra].
    reflexivity.
Qed.