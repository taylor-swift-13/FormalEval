Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; 25.12472520208241%R; (-2.6958053769612267)%R; 33.195768044846155%R; (-1.9199320509072952)%R]
                    [9.9%R; 25.12472520208241%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (Hpos1 : 0 < 9.9%R) by lra.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1].
  - simpl.
    assert (Hpos2 : 0 < 25.12472520208241%R) by lra.
    destruct (Rlt_dec 0 25.12472520208241%R) as [H2|H2].
    + simpl.
      assert (Hneg3 : ~(0 < (-2.6958053769612267)%R)) by lra.
      destruct (Rlt_dec 0 (-2.6958053769612267)%R) as [H3|H3].
      * exfalso. apply Hneg3. exact H3.
      * simpl.
        assert (Hpos4 : 0 < 33.195768044846155%R) by lra.
        destruct (Rlt_dec 0 33.195768044846155%R) as [H4|H4].
        -- simpl.
           assert (Hneg5 : ~(0 < (-1.9199320509072952)%R)) by lra.
           destruct (Rlt_dec 0 (-1.9199320509072952)%R) as [H5|H5].
           ** exfalso. apply Hneg5. exact H5.
           ** simpl. reflexivity.
        -- exfalso. apply H4. exact Hpos4.
    + exfalso. apply H2. exact Hpos2.
  - exfalso. apply H1. exact Hpos1.
Qed.