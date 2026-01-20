Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0%R; (-5 / 4)%R; (-3 / 2)%R; (-3 / 4)%R; (-9 / 4)%R; (-2)%R; (-3)%R; (-4)%R; (-5)%R; (-6)%R]
    [].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 0) as [H0|H0]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 ((-5) / 4)) as [H1|H1]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 ((-3) / 2)) as [H2|H2]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 ((-3) / 4)) as [H3|H3]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 ((-9) / 4)) as [H4|H4]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 (-2)) as [H5|H5]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 (-3)) as [H6|H6]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 (-4)) as [H7|H7]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 (-5)) as [H8|H8]; try (exfalso; lra); simpl.
  destruct (Rlt_dec 0 (-6)) as [H9|H9]; try (exfalso; lra); simpl.
  reflexivity.
Qed.