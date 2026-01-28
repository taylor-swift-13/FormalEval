Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition common_spec (l1 l2 out : list Z) : Prop :=
  NoDup out
  /\ Sorted Z.le out
  /\ forall x : Z, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [1; 1; 1; 2; 2; 2; 3; 3; 3; 1] 
    [8; 7; 6; 10; 5] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    constructor.
  - split.
    + (* Prove Sorted Z.le out *)
      constructor.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition; subst; try lia.
Qed.