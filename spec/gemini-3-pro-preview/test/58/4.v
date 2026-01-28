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
    [4%Z; 3%Z; 2%Z; 8%Z] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - constructor.
  - split.
    + constructor.
    + intros x. split.
      * intro H. simpl in H. contradiction.
      * intros [_ H2]. simpl in H2. contradiction.
Qed.