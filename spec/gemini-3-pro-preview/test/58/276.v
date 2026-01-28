Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition common_spec (l1 l2 res : list R) : Prop :=
  Sorted Rle res /\
  NoDup res /\
  (forall x : R, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [-49.59113788406315%R; -15.823575020711672%R; -50.75064768360904%R; 43.025195515136005%R; 87.01345659296072%R; -57.351923170295606%R]
    [] 
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
        intro H. inversion H.
      * (* <- *)
        intros [H1 H2]. inversion H2.
Qed.