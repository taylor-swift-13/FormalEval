Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  implb b1 b2 = true.

Definition unique_spec (l : list bool) (res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  forall x : bool, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [false; true; false; false; true; false] [false; true].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted bool_le res *)
    repeat constructor.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intuition; try discriminate.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 20.
Qed.