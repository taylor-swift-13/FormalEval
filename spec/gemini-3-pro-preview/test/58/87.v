Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition common_spec (l1 l2 res : list R) : Prop :=
  Sorted Rle res /\
  NoDup res /\
  (forall x : R, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [75.77463522981091%R; -68.50801238200772%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R; -16.457158264907306%R] 
    [75.77463522981091%R; -68.50801238200772%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R; -16.457158264907306%R] 
    [-68.50801238200772%R; -50.826346308865425%R; -16.457158264907306%R; -14.710649879972792%R; 62.25940015569594%R; 75.77463522981091%R; 94.08151854781187%R].
Proof.
  unfold common_spec.
  split.
  - repeat constructor; simpl; try lra.
  - split.
    + repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [try lra | ]); contradiction.
    + intros x. split.
      * intro H. simpl in H.
        repeat (destruct H as [H|H]; [subst; simpl; tauto | ]); contradiction.
      * intros [H1 H2]. simpl in H1.
        repeat (destruct H1 as [H1|H1]; [
          subst; simpl; tauto
        | ]); contradiction.
Qed.