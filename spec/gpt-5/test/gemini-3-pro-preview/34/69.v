Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition bool_le (x y : bool) : Prop :=
  match x, y with
  | false, _ => True
  | _, true => True
  | true, false => False
  end.

Definition unique_spec (l : list bool) (res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  forall x : bool, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [false; false; true; true] [false; true].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor.
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto.
      * repeat destruct H as [H|H]; subst; auto.
Qed.