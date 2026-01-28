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

Definition common_spec (l1 l2 res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  (forall x : bool, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [true; false; false; false; true; false; false; true; false; true; false]
    [true; false; false; false; true; false; false; true; false; true; false]
    [false; true].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    unfold bool_le.
    repeat constructor.
  - split.
    + (* NoDup *)
      constructor.
      * simpl. intros [H|H]; [discriminate|contradiction].
      * constructor.
        -- simpl. tauto.
        -- constructor.
    + (* Equivalence *)
      intros x. split.
      * intros _. split.
        -- destruct x; simpl; tauto.
        -- destruct x; simpl; tauto.
      * intros _.
        destruct x; simpl; tauto.
Qed.