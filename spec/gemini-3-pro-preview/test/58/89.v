Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (a b : bool) : Prop := implb a b = true.

Definition common_spec (l1 l2 res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  (forall x : bool, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [true; false; false; false; false; true; false; false; true; false; false; false] 
    [true; false; false; false; false; true; false; false; true; false; false; false] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    unfold bool_le. repeat constructor.
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [try discriminate | ]); contradiction.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H.
        destruct x; split; simpl; tauto.
      * (* <- *)
        intros [H1 H2].
        destruct x; simpl; tauto.
Qed.