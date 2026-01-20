Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [10.791699079028088%R; 25.221353337136023%R; 25.376288083829433%R; -3.1836537136945844%R; -2.6958053769612267%R; -1.5%R]
    [10.791699079028088%R; 25.221353337136023%R; 25.376288083829433%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 10.791699079028088%R) as [H1|H1].
  - destruct (Rlt_dec 0 25.221353337136023%R) as [H2|H2].
    + destruct (Rlt_dec 0 25.376288083829433%R) as [H3|H3].
      * destruct (Rlt_dec 0 (-3.1836537136945844%R)) as [H4|H4].
        { assert (~ 0 < -3.1836537136945844%R) by lra. contradiction. }
        { destruct (Rlt_dec 0 (-2.6958053769612267%R)) as [H5|H5].
          { assert (~ 0 < -2.6958053769612267%R) by lra. contradiction. }
          { destruct (Rlt_dec 0 (-1.5%R)) as [H6|H6].
            { assert (~ 0 < -1.5%R) by lra. contradiction. }
            { reflexivity. } } }
      * assert (0 < 25.376288083829433%R) by lra. contradiction.
    + assert (0 < 25.221353337136023%R) by lra. contradiction.
  - assert (0 < 10.791699079028088%R) by lra. contradiction.
Qed.