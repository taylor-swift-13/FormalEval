Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; IZR 0%Z; IZR (-4)%Z; 2.5%R; IZR 5%Z; (-2.2)%R; IZR (-8)%Z; 7.7%R; 9.9%R; (-10.5)%R]
    [0.5%R; 2.5%R; IZR 5%Z; 7.7%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 0.5 0) as [H1|H1].
  - simpl.
    destruct (Rgt_dec 0 0) as [H2|H2].
    + exfalso. lra.
    + simpl.
      destruct (Rgt_dec (-4) 0) as [H3|H3].
      * exfalso. lra.
      * simpl.
        destruct (Rgt_dec 2.5 0) as [H4|H4].
        -- simpl.
           destruct (Rgt_dec 5 0) as [H5|H5].
           ++ simpl.
              destruct (Rgt_dec (-2.2) 0) as [H6|H6].
              ** exfalso. lra.
              ** simpl.
                 destruct (Rgt_dec (-8) 0) as [H7|H7].
                 --- exfalso. lra.
                 --- simpl.
                     destruct (Rgt_dec 7.7 0) as [H8|H8].
                     +++ simpl.
                         destruct (Rgt_dec 9.9 0) as [H9|H9].
                         *** simpl.
                             destruct (Rgt_dec (-10.5) 0) as [H10|H10].
                             ---- exfalso. lra.
                             ---- simpl. reflexivity.
                         *** exfalso. apply H9. lra.
                     +++ exfalso. apply H8. lra.
           ++ exfalso. apply H5. lra.
        -- exfalso. apply H4. lra.
  - exfalso. apply H1. lra.
Qed.