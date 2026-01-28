Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | true, false => False
  | _, _ => True
  end.

Definition unique_spec (l : list bool) (res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  forall x : bool, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [false; false; false; true; true] [false; true].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted bool_le res *)
    repeat constructor.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intro H; destruct H; try discriminate; try contradiction.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 20.
Qed.