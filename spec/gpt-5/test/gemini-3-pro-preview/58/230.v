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
    [11; 1; 2; 3; 12; 10; 8; 9] 
    [11; 1; 2; 3; 12; 10; 8; 9] 
    [1; 2; 3; 8; 9; 10; 11; 12].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    repeat constructor; simpl; intuition; lia.
  - split.
    + (* Prove Sorted Z.le out *)
      repeat constructor; simpl; try lia.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition; subst; try lia.
Qed.