Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [9.9%R; 25.221353337136023%R; 24.93175152910768%R; -3.1836537136945844%R; -3.1836537136945844%R; -0.75%R; -1.5%R]
    [9.9%R; 25.221353337136023%R; 24.93175152910768%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 25.221353337136023%R) as [H2|H2]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 24.93175152910768%R) as [H3|H3]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-3.1836537136945844%R)) as [H4|H4].
  - exfalso; lra.
  - simpl.
    destruct (Rlt_dec 0 (-3.1836537136945844%R)) as [H5|H5].
    + exfalso; lra.
    + simpl.
      destruct (Rlt_dec 0 (-0.75%R)) as [H6|H6].
      * exfalso; lra.
      * simpl.
        destruct (Rlt_dec 0 (-1.5%R)) as [H7|H7].
        -- exfalso; lra.
        -- simpl.
           reflexivity.
Qed.