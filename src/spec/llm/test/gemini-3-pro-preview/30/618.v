Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [1.2; 2.5; 3.7] [1.2; 2.5; 3.7].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 1.2 0) as [_ | H1].
  - destruct (Rgt_dec 2.5 0) as [_ | H2].
    + destruct (Rgt_dec 3.7 0) as [_ | H3].
      * reflexivity.
      * exfalso. apply H3.
        unfold Rdiv. apply Rmult_gt_0_compat.
        { apply IZR_lt. reflexivity. }
        { apply Rinv_0_lt_compat. apply IZR_lt. reflexivity. }
    + exfalso. apply H2.
      unfold Rdiv. apply Rmult_gt_0_compat.
      { apply IZR_lt. reflexivity. }
      { apply Rinv_0_lt_compat. apply IZR_lt. reflexivity. }
  - exfalso. apply H1.
    unfold Rdiv. apply Rmult_gt_0_compat.
    { apply IZR_lt. reflexivity. }
    { apply Rinv_0_lt_compat. apply IZR_lt. reflexivity. }
Qed.