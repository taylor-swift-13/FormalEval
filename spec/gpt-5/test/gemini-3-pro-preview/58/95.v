Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition bool_le (x y : bool) : Prop :=
  match x, y with
  | true, false => False
  | _, _ => True
  end.

Definition common_spec (l1 l2 out : list bool) : Prop :=
  NoDup out
  /\ Sorted bool_le out
  /\ forall x : bool, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [true; false; false; false; true; false; false; true; false; false; false; false] 
    [true; false; false; false; true; false; false; true; false; false; false; false] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - repeat constructor.
    + simpl; intuition; discriminate.
    + simpl; intuition.
  - split.
    + unfold bool_le. repeat constructor.
    + intros x.
      simpl.
      destruct x; intuition.
Qed.