Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition unique_spec (l : list Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  forall x : Z, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [1; 2; 2; 3; 4; 4; 5; 6; 7; 7; 7; 8; -4; 8; 8; 9; 9; 9; 10; 9] [-4; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted Z.le res *)
    repeat constructor; simpl; try lia.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intuition; try lia.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto 50.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 50.
Qed.