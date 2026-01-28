Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | false, _ => True
  | true, true => True
  | true, false => False
  end.

Definition common_spec (l1 l2 out : list bool) : Prop :=
  NoDup out
  /\ Sorted bool_le out
  /\ forall x : bool, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [true; false; false; false; false; true; false; false; true; false; false; false] 
    [true; false; false; false; false; true; false; false; true; false; false; false] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - repeat constructor; simpl; intuition; discriminate.
  - split.
    + repeat constructor; simpl; auto.
    + intros x.
      simpl.
      destruct x; intuition.
Qed.