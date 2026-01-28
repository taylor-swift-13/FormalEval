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
    [1%Z; 2%Z; 3%Z] 
    [4%Z; 5%Z] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    constructor.
  - split.
    + (* NoDup *)
      constructor.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H. simpl in H. contradiction.
      * (* <- *)
        intros [H1 H2]. simpl in H1. simpl in H2.
        repeat (destruct H1 as [H1|H1]; [
          subst; intuition lia
        | ]); contradiction.
Qed.