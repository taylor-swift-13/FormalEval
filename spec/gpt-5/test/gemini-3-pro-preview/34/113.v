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
  unique_spec 
    [1.2; 3; 2.1; 5; 3; 123; 2; 3; 3; 9; 0; 123; -1; 2.1; 2.1; 3; 9.9; 0.1; 0.3; 123] 
    [-1; 0; 0.1; 0.3; 1.2; 2; 2.1; 3; 5; 9; 9.9; 123].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; try lra.
  - split.
    + repeat constructor; simpl; intro H; repeat destruct H as [H|H]; try lra.
    + intro x; simpl; split; intro H; repeat destruct H as [H|H]; subst; tauto.
Qed.