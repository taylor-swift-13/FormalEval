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
  common_spec [] [] [].
Proof.
  unfold common_spec.
  split.
  - constructor.
  - split.
    + constructor.
    + intros x. simpl. tauto.
Qed.