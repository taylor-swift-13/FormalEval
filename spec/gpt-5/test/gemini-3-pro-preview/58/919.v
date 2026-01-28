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
    [9; 0; 6; 4; 6; 5; 10; 5; 9; 0; 10] 
    [9; 0; 6; 4; 6; 5; 10; 5; 9; 0; 10] 
    [0; 4; 5; 6; 9; 10].
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