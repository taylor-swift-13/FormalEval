Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition unique_spec (l : list Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  forall x : Z, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec [] [].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted Z.le res *)
    constructor.
  - split.
    + (* Prove NoDup res *)
      constructor.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H; contradiction.
Qed.