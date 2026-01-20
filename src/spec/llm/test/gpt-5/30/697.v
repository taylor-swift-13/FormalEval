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
  get_positive_spec
    [7.878953248636265%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R]
    [7.878953248636265%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  assert (H1 : 7.878953248636265%R > 0%R) by lra.
  assert (H2 : 25.12472520208241%R > 0%R) by lra.
  assert (H3 : 33.195768044846155%R > 0%R) by lra.
  assert (Hneg : ~ (-2.25%R > 0%R)) by lra.
  destruct (Rgt_dec 7.878953248636265%R 0%R) as [P1|N1].
  - simpl.
    destruct (Rgt_dec 25.12472520208241%R 0%R) as [P2|N2].
    + simpl.
      destruct (Rgt_dec 33.195768044846155%R 0%R) as [P3|N3].
      * simpl.
        destruct (Rgt_dec (-2.25%R) 0%R) as [P4|N4].
        { contradiction. }
        simpl.
        destruct (Rgt_dec 33.195768044846155%R 0%R) as [P5|N5].
        { simpl. reflexivity. }
        { exfalso. apply N5. exact H3. }
      * exfalso. apply N3. exact H3.
    + exfalso. apply N2. exact H2.
  - exfalso. apply N1. exact H1.
Qed.