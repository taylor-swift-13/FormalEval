Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [9.9%R; 24.93175152910768%R; -3.1836537136945844%R; -3.1836537136945844%R; -0.42322814636615796%R]
    [9.9%R; 24.93175152910768%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (H1 : 9.9%R > 0) by lra.
  destruct (Rgt_dec 9.9%R 0) as [H1'|H1'].
  - simpl.
    assert (H2 : 24.93175152910768%R > 0) by lra.
    destruct (Rgt_dec 24.93175152910768%R 0) as [H2'|H2'].
    + simpl.
      assert (H3 : ~ (-3.1836537136945844%R) > 0) by lra.
      destruct (Rgt_dec (-3.1836537136945844%R) 0) as [H3'|H3'].
      * exfalso. apply H3. exact H3'.
      * simpl.
        assert (H4 : ~ (-3.1836537136945844%R) > 0) by lra.
        destruct (Rgt_dec (-3.1836537136945844%R) 0) as [H4'|H4'].
        -- exfalso. apply H4. exact H4'.
        -- simpl.
           assert (H5 : ~ (-0.42322814636615796%R) > 0) by lra.
           destruct (Rgt_dec (-0.42322814636615796%R) 0) as [H5'|H5'].
           ++ exfalso. apply H5. exact H5'.
           ++ simpl. reflexivity.
    + exfalso. apply H2'. exact H2.
  - exfalso. apply H1'. exact H1.
Qed.