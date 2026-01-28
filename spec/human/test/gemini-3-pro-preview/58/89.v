Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `common` *)
Definition problem_58_pre (l1 l2 : list bool) : Prop := True.

Definition bool_le (b1 b2 : bool) : Prop := implb b1 b2 = true.

Definition problem_58_spec (l1 l2 l_out: list bool) : Prop :=
  (* Condition 1: Commonality and Completeness *)
  (* l_out contains x iff x is in both l1 and l2 *)
  (forall x: bool, In x l_out <-> (In x l1 /\ In x l2)) /\

  (* Condition 2: Ordered *)
  (* l_out is sorted by bool_le *)
  Sorted bool_le l_out /\

  (* Condition 3: Uniqueness *)
  (* l_out has no duplicates *)
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [true; false; false; false; false; true; false; false; true; false; false; false]
    [true; false; false; false; false; true; false; false; true; false; false; false]
    [false; true].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x.
    destruct x.
    + (* x = true *)
      simpl. split; auto 20.
    + (* x = false *)
      simpl. split; auto 20.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      unfold bool_le.
      repeat (constructor; simpl; auto).
    + (* NoDup *)
      repeat constructor; simpl; intuition discriminate.
Qed.