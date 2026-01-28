Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition bool_le (x y : bool) : Prop :=
  match x, y with
  | true, false => False
  | _, _ => True
  end.

Definition unique_spec (l : list bool) (res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  forall x : bool, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [true; true; false; false; true; true] [false; true].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; auto.
  - split.
    + repeat constructor; simpl; intuition; try discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.