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
    [72.37521383648374%R; 75.77463522981091%R; -68.50801238200772%R; -16.457158264907306%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R] 
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