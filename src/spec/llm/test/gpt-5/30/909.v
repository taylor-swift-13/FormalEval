Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; -2.8683444012540678%R; 25.12472520208241%R; 9.9%R; 12.997289062694836%R]
                    [9.9%R; 25.12472520208241%R; 9.9%R; 12.997289062694836%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 9.9%R 0) as [H1|H1].
  - simpl.
    destruct (Rgt_dec (-2.8683444012540678%R) 0) as [H2|H2].
    + exfalso. lra.
    + simpl.
      destruct (Rgt_dec 25.12472520208241%R 0) as [H3|H3].
      * simpl.
        destruct (Rgt_dec 9.9%R 0) as [H4|H4].
        -- simpl.
           destruct (Rgt_dec 12.997289062694836%R 0) as [H5|H5].
           ++ simpl. reflexivity.
           ++ exfalso. apply H5. lra.
        -- exfalso. apply H4. lra.
      * exfalso. apply H3. lra.
  - exfalso. apply H1. lra.
Qed.