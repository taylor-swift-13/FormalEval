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
  unique_spec [1; -1; 0; 0; 1; -1; 0; 0; -1.2893213949526219; 0.00001; 0.00001; 10000000000; -10000000000; 0.0000000001; -0.0000000001] 
              [-10000000000; -1.2893213949526219; -1; -0.0000000001; 0; 0.0000000001; 0.00001; 1; 10000000000].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; try lra.
  - split.
    + repeat constructor; simpl; intuition; try lra.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.