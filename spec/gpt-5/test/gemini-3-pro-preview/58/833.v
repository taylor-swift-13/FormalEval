Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.

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
    [true; true; false; true; true; false; false; false] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - constructor.
  - split.
    + constructor.
    + intros x. simpl. intuition.
Qed.