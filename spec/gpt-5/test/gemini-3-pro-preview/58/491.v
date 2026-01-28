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
    [6; 4; 1; 4] 
    [6; 4; 1; 4] 
    [1; 4; 6].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    repeat constructor.
    + simpl; intuition; lia.
    + simpl; intuition; lia.
    + simpl; intuition; lia.
  - split.
    + (* Prove Sorted Z.le out *)
      repeat constructor; simpl; try lia.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      (* The goal is now a propositional logic formula with Z equalities.
         intuition breaks down logical connectives (/\, \/, <->, ->).
         subst replaces variables with values (e.g., x = 1).
         lia solves linear integer arithmetic (e.g., 1 <> 4). *)
      intuition; subst; try lia.
Qed.