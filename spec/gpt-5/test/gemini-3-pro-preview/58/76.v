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
    [-66.80587176097761%R; 61.566275072399776%R; -74.68836438529377%R; -0.19883232278070295%R; -0.6234234911641607%R; -50.826346308865425%R; -58.86766032411499%R; 62.25940015569594%R; 95.27559980134242%R] 
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