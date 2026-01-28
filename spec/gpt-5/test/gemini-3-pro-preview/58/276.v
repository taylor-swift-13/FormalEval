Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition common_spec (l1 l2 out : list R) : Prop :=
  NoDup out
  /\ Sorted Rle out
  /\ forall x : R, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [-49.59113788406315; -15.823575020711672; -50.75064768360904; 43.025195515136005; 87.01345659296072; -57.351923170295606] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    repeat constructor.
  - split.
    + (* Prove Sorted Rle out *)
      repeat constructor.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition.
Qed.