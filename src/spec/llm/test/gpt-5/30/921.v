Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [-10.5%R; 25.12472520208241%R; -1.5%R; -2.25%R] [25.12472520208241%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec (-10.5%R) 0%R) as [H1|H1].
  - assert (Hle1: -10.5%R <= 0%R) by lra. exfalso. apply (Rle_not_gt _ _ Hle1). exact H1.
  - simpl.
    destruct (Rgt_dec 25.12472520208241%R 0%R) as [H2|H2].
    + simpl.
      destruct (Rgt_dec (-1.5%R) 0%R) as [H3|H3].
      * assert (Hle3: -1.5%R <= 0%R) by lra. exfalso. apply (Rle_not_gt _ _ Hle3). exact H3.
      * simpl.
        destruct (Rgt_dec (-2.25%R) 0%R) as [H4|H4].
        -- assert (Hle4: -2.25%R <= 0%R) by lra. exfalso. apply (Rle_not_gt _ _ Hle4). exact H4.
        -- simpl. reflexivity.
    + exfalso. apply H2. lra.
Qed.