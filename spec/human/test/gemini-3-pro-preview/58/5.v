Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `common` *)
Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (* Condition 1: Commonality and Completeness *)
  (* l_out contains x iff x is in both l1 and l2 *)
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\

  (* Condition 2: Ordered *)
  (* l_out is sorted by Z.le *)
  Sorted Z.le l_out /\

  (* Condition 3: Uniqueness *)
  (* l_out has no duplicates *)
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [1; 2; 3]
    [1; 2; 3]
    [1; 2; 3].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x; split.
    + (* -> *)
      intro H. split; assumption.
    + (* <- *)
      intros [H1 H2]. assumption.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      repeat constructor.
      all: simpl; try lia.
    + (* NoDup *)
      repeat constructor.
      all: simpl; intuition lia.
Qed.