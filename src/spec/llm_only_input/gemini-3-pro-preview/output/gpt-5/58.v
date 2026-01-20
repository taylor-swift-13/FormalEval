Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Psatz.

Import ListNotations.
Open Scope Z_scope.

Definition common_spec (l1 l2 out : list Z) : Prop :=
  NoDup out
  /\ Sorted Z.le out
  /\ forall x : Z, In x out <-> (In x l1 /\ In x l2).

Example test_common : common_spec
  [1; 4; 3; 34; 653; 2; 5]
  [5; 7; 1; 5; 9; 653; 121]
  [1; 5; 653].
Proof.
  unfold common_spec.
  split.
  - (* Part 1: NoDup out *)
    repeat constructor; simpl; intuition discriminate.
  - split.
    + (* Part 2: Sorted out *)
      repeat constructor; simpl; try lia.
    + (* Part 3: Equivalence of membership *)
      intro x. split; intro H.
      * (* Direction: In x out -> In x l1 /\ In x l2 *)
        simpl in H.
        (* Destruct the finite possibilities of x being in out *)
        repeat destruct H as [H|H]; subst; simpl; split; try tauto; try lia.
      * (* Direction: In x l1 /\ In x l2 -> In x out *)
        destruct H as [H1 H2].
        simpl in H1, H2.
        (* Iterate through all elements of l1 (H1) *)
        repeat (destruct H1 as [H1|H1]; [ 
          (* Case: x is specific element from l1. 
             Check if it is in l2 (H2). If so, prove it is in out. 
             If not, lia/tauto finds the contradiction. *)
          subst; simpl in *; try tauto; try lia 
        | ]).
        (* Handle the last element of l1 *)
        subst; simpl in *; try tauto; try lia.
Qed.