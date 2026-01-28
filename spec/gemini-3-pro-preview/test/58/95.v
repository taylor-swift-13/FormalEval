Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | true, false => False
  | _, _ => True
  end.

Definition common_spec (l1 l2 res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  (forall x : bool, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [true; false; false; false; true; false; false; true; false; false; false; false] 
    [true; false; false; false; true; false; false; true; false; false; false; false] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    repeat (constructor; simpl).
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [try discriminate | ]); contradiction.
    + (* Equivalence *)
      intros x; destruct x; simpl; split; tauto.
Qed.