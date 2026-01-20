Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; -2.6958053769612267%R; 25.12472520208241%R; 0.5%R; -2.6958053769612267%R]
                    [9.9%R; 25.12472520208241%R; 0.5%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  destruct (Rgt_dec 9.9%R 0) as [H1|H1].
  - simpl.
    unfold Rgtb.
    destruct (Rgt_dec (-2.6958053769612267%R) 0) as [H2|H2].
    + exfalso. apply Rgt_not_le in H2. lra.
    + simpl.
      unfold Rgtb.
      destruct (Rgt_dec 25.12472520208241%R 0) as [H3|H3].
      * simpl.
        unfold Rgtb.
        destruct (Rgt_dec 0.5%R 0) as [H4|H4].
        -- simpl.
           unfold Rgtb.
           destruct (Rgt_dec (-2.6958053769612267%R) 0) as [H5|H5].
           ++ exfalso. apply Rgt_not_le in H5. lra.
           ++ simpl. reflexivity.
        -- exfalso. apply H4. lra.
      * exfalso. apply H3. lra.
  - exfalso. apply H1. lra.
Qed.