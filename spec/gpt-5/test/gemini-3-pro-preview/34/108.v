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
  unique_spec [1; -1; 0; 0; 1; -1; 0; 0; 1/100000; 1/100000; 10000000000; -10000000000; 1/10000000000; -1/10000000000] 
              [-10000000000; -1; -1/10000000000; 0; 1/10000000000; 1/100000; 1; 10000000000].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted Rle res *)
    repeat constructor; simpl; try lra.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intuition; try lra.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; try lra; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; try lra; auto 20.
Qed.