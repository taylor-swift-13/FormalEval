Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0%R) l.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; 0%R; (-4)%R; 5%R; (-2.6307909667819085)%R; (-2.651030586877352)%R; (-8)%R; 7.7%R; 9.9%R; (-10.5)%R; 9.9%R]
    [0.5%R; 5%R; 7.7%R; 9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  simpl.
  destruct (Rgt_dec 0.5%R 0%R) as [H1|H1].
  - simpl.
    destruct (Rgt_dec 0%R 0%R) as [H2|H2].
    + exfalso. lra.
    + simpl.
      destruct (Rgt_dec (-4)%R 0%R) as [H3|H3].
      * exfalso. lra.
      * simpl.
        destruct (Rgt_dec 5%R 0%R) as [H4|H4].
        -- simpl.
           destruct (Rgt_dec (-2.6307909667819085)%R 0%R) as [H5|H5].
           ++ exfalso. lra.
           ++ simpl.
              destruct (Rgt_dec (-2.651030586877352)%R 0%R) as [H6|H6].
              ** exfalso. lra.
              ** simpl.
                 destruct (Rgt_dec (-8)%R 0%R) as [H7|H7].
                 --- exfalso. lra.
                 --- simpl.
                     destruct (Rgt_dec 7.7%R 0%R) as [H8|H8].
                     +++ simpl.
                         destruct (Rgt_dec 9.9%R 0%R) as [H9|H9].
                         **** simpl.
                              destruct (Rgt_dec (-10.5)%R 0%R) as [H10|H10].
                              ***** exfalso. lra.
                              ***** simpl.
                                    destruct (Rgt_dec 9.9%R 0%R) as [H11|H11].
                                    ------ simpl. reflexivity.
                                    ------ exfalso. assert (9.9%R > 0%R) by lra. contradiction.
                         **** exfalso. assert (9.9%R > 0%R) by lra. contradiction.
                     +++ exfalso. assert (7.7%R > 0%R) by lra. contradiction.
        -- exfalso. assert (5%R > 0%R) by lra. contradiction.
  - exfalso. assert (0.5%R > 0%R) by lra. contradiction.
Qed.