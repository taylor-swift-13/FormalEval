Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition common_spec (l1 l2 res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  (forall x : Z, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [1%Z; 2%Z; 3%Z; 4%Z] 
    [1%Z; 2%Z; 3%Z; 4%Z] 
    [1%Z; 2%Z; 3%Z; 4%Z].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    repeat constructor; simpl; lia.
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [try lia | ]); contradiction.
    + (* Equivalence *)
      intros x. split.
      * intro H. split; assumption.
      * intros [H _]. assumption.
Qed.