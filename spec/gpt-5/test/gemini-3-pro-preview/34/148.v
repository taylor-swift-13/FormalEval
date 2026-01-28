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
  unique_spec [5555555555555555555555; 0; 5555555555555555555555; 2; -999999999999999999999999999999999; -5555555555555555555555; 9] [-999999999999999999999999999999999; -5555555555555555555555; 0; 2; 9; 5555555555555555555555].
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
        repeat destruct H as [H|H]; subst; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 20.
Qed.