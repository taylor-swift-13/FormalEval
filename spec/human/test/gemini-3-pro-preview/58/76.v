Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `common` *)
Definition problem_58_pre (l1 l2 : list R) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list R) : Prop :=
  (* Condition 1: Commonality and Completeness *)
  (* l_out contains x iff x is in both l1 and l2 *)
  (forall x: R, In x l_out <-> (In x l1 /\ In x l2)) /\

  (* Condition 2: Ordered *)
  (* l_out is sorted by Rle *)
  Sorted Rle l_out /\

  (* Condition 3: Uniqueness *)
  (* l_out has no duplicates *)
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [-66.80587176097761%R; 61.566275072399776%R; -74.68836438529377%R; -0.19883232278070295%R; -0.6234234911641607%R; -50.826346308865425%R; -58.86766032411499%R; 62.25940015569594%R; 95.27559980134242%R]
    []
    [].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x; split.
    + (* -> : If x in output, then x in l1 and l2 *)
      intro H.
      inversion H.
    + (* <- : If x in l1 and l2, then x in output *)
      intros [H1 H2].
      inversion H2.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      constructor.
    + (* NoDup *)
      constructor.
Qed.