Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition unique_spec (l : list R) (res : list R) : Prop :=
  Sorted Rle res /\
  NoDup res /\
  forall x : R, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [3.0219968583931567; 1.1; 2.2; 4.4; 4.4; 3.0219968583931567; 2.2] 
              [1.1; 2.2; 3.0219968583931567; 4.4].
Proof.
  unfold unique_spec.
  split.
  - 
    repeat constructor; simpl; try lra.
  - split.
    + 
      repeat constructor; simpl; intuition; try lra.
    + 
      intro x.
      simpl.
      split; intro H.
      * 
        repeat destruct H as [H|H]; subst; auto 20.
      * 
        repeat destruct H as [H|H]; subst; auto 20.
Qed.