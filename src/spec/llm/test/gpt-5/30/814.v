Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [-2.651030586877352%R; (-4)%R; 2.5%R; 5%R; -2.651030586877352%R; (-8)%R; 8.193677988449515%R; 7.7%R; 9.9%R; (-10.5)%R; -0.42322814636615796%R; -2.2%R]
    [2.5%R; 5%R; 8.193677988449515%R; 7.7%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (-2.651030586877352%R)) as [H1|H1].
  - exfalso; lra.
  - simpl.
    destruct (Rlt_dec 0 ((-4)%R)) as [H2|H2].
    + exfalso; lra.
    + simpl.
      destruct (Rlt_dec 0 (2.5%R)) as [H3|H3].
      * simpl.
        destruct (Rlt_dec 0 (5%R)) as [H4|H4].
        -- simpl.
           destruct (Rlt_dec 0 (-2.651030586877352%R)) as [H5|H5].
           --- exfalso; lra.
           --- simpl.
               destruct (Rlt_dec 0 ((-8)%R)) as [H6|H6].
               ---- exfalso; lra.
               ---- simpl.
                    destruct (Rlt_dec 0 (8.193677988449515%R)) as [H7|H7].
                    ----- simpl.
                          destruct (Rlt_dec 0 (7.7%R)) as [H8|H8].
                          ------ simpl.
                                  destruct (Rlt_dec 0 (9.9%R)) as [H9|H9].
                                  ------- simpl.
                                          destruct (Rlt_dec 0 ((-10.5)%R)) as [H10|H10].
                                          -------- exfalso; lra.
                                          -------- simpl.
                                                   destruct (Rlt_dec 0 (-0.42322814636615796%R)) as [H11|H11].
                                                   --------- exfalso; lra.
                                                   --------- simpl.
                                                             destruct (Rlt_dec 0 (-2.2%R)) as [H12|H12].
                                                             ---------- exfalso; lra.
                                                             ---------- simpl.
                                                                         reflexivity.
                                  ------- exfalso; lra.
                          ------ exfalso; lra.
                    ----- exfalso; lra.
        -- exfalso; lra.
      * exfalso; lra.
Qed.