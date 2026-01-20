Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [21.28666897792971%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; -3.1836537136945844%R; -1.5%R]
    [21.28666897792971%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 21.28666897792971%R 0%R) as [H1|H1].
  - simpl.
    destruct (Rgt_dec 25.221353337136023%R 0%R) as [H2|H2].
    + simpl.
      destruct (Rgt_dec 24.93175152910768%R 0%R) as [H3|H3].
      * simpl.
        destruct (Rgt_dec 33.195768044846155%R 0%R) as [H4|H4].
        -- simpl.
           destruct (Rgt_dec (-3.1836537136945844%R) 0%R) as [H5|H5].
           ++ exfalso. apply (Rgt_not_le _ _ H5). lra.
           ++ simpl.
              destruct (Rgt_dec (-1.5%R) 0%R) as [H6|H6].
              ** exfalso. apply (Rgt_not_le _ _ H6). lra.
              ** simpl. reflexivity.
        -- exfalso. apply H4. lra.
      * exfalso. apply H3. lra.
    + exfalso. apply H2. lra.
  - exfalso. apply H1. lra.
Qed.