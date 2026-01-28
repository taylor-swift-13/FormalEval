Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | true, false => False
  | _, _ => True
  end.

Definition common_spec (l1 l2 out : list bool) : Prop :=
  NoDup out
  /\ Sorted bool_le out
  /\ forall x : bool, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [true; false; false; false; true; false; false; true; false; true; false; false] 
    [true; false; false; false; true; false; false; true; false; true; false; false] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - repeat constructor; simpl; intuition; discriminate.
  - split.
    + repeat constructor.
    + intros x.
      simpl.
      destruct x; intuition.
Qed.