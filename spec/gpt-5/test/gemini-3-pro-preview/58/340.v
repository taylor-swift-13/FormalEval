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
    [8; 9; 9; 9; 10; 10; 10] 
    [8; 9; 9; 9; 10; 10; 10] 
    [8; 9; 10].
Proof.
  unfold common_spec.
  split.
  - repeat constructor.
    + simpl; intuition; lia.
    + simpl; intuition; lia.
    + simpl; intuition; lia.
  - split.
    + repeat constructor; simpl; try lia.
    + intros x.
      simpl.
      intuition; subst; try lia.
Qed.