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
    [1; 2; -45; 4] 
    [34; 4; 5; 8; 6; 6] 
    [4].
Proof.
  unfold common_spec.
  split.
  - repeat constructor.
    simpl; intuition.
  - split.
    + repeat constructor; simpl; try lia.
    + intros x.
      simpl.
      intuition; subst; try lia.
Qed.