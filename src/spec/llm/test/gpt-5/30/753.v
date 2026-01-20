Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; 25.221353337136023%R; 24.93175152910768%R; -0.42322814636615796%R; 33.195768044846155%R; -2.6307909667819085%R; -2.25%R] [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 9.9%R 0%R) as [H1|H1].
  - simpl.
    destruct (Rgt_dec 25.221353337136023%R 0%R) as [H2|H2].
    + simpl.
      destruct (Rgt_dec 24.93175152910768%R 0%R) as [H3|H3].
      * simpl.
        destruct (Rgt_dec (-0.42322814636615796%R) 0%R) as [H4|H4].
        -- exfalso; lra.
        -- simpl.
           destruct (Rgt_dec 33.195768044846155%R 0%R) as [H5|H5].
           ++ simpl.
              destruct (Rgt_dec (-2.6307909667819085%R) 0%R) as [H6|H6].
              ** exfalso; lra.
              ** simpl.
                 destruct (Rgt_dec (-2.25%R) 0%R) as [H7|H7].
                 --- exfalso; lra.
                 --- simpl. reflexivity.
           ++ exfalso; lra.
      * exfalso; lra.
    + exfalso; lra.
  - exfalso; lra.
Qed.