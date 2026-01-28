Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | false, _ => True
  | true, true => True
  | true, false => False
  end.

Definition unique_spec (l : list bool) (res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  forall x : bool, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [true; false; false; true] [false; true].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted bool_le res *)
    repeat constructor; simpl; auto.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intuition; discriminate.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto.
Qed.