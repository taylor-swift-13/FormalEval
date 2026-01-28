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
    [72.37521383648374%R; 75.77463522981091%R; -68.50801238200772%R; -16.457158264907306%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R]
    []
    [].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x; split.
    + (* -> : If x in output, then x in l1 and l2 *)
      intro H.
      (* Output is empty, so H is False *)
      inversion H.
    + (* <- : If x in l1 and l2, then x in output *)
      intros [H1 H2].
      (* l2 is empty, so H2 is False *)
      inversion H2.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      constructor.
    + (* NoDup *)
      constructor.
Qed.