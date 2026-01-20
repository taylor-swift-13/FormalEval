Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [0.5%R; (-4)%R; 2.5%R; 5%R; (-2.2)%R; (-8)%R; (-7)%R; 9.9%R; (-11.18889279027017)%R; (-10.5)%R]
                    [0.5%R; 2.5%R; 5%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 0.5) as [H1|H1].
  - simpl.
    destruct (Rlt_dec 0 (-4)) as [H2|H2].
    + exfalso; lra.
    + simpl.
      destruct (Rlt_dec 0 2.5) as [H3|H3].
      * simpl.
        destruct (Rlt_dec 0 5) as [H4|H4].
        -- simpl.
           destruct (Rlt_dec 0 (-2.2)) as [H5|H5].
           ++ exfalso; lra.
           ++ simpl.
              destruct (Rlt_dec 0 (-8)) as [H6|H6].
              ** exfalso; lra.
              ** simpl.
                 destruct (Rlt_dec 0 (-7)) as [H7|H7].
                 --- exfalso; lra.
                 --- simpl.
                     destruct (Rlt_dec 0 9.9) as [H8|H8].
                     +++ simpl.
                         destruct (Rlt_dec 0 (-11.18889279027017)) as [H9|H9].
                         *** exfalso; lra.
                         *** simpl.
                             destruct (Rlt_dec 0 (-10.5)) as [H10|H10].
                             ---- exfalso; lra.
                             ---- simpl. reflexivity.
                     +++ exfalso; apply H8; lra.
        -- exfalso; apply H4; lra.
      * exfalso; apply H3; lra.
  - exfalso; apply H1; lra.
Qed.