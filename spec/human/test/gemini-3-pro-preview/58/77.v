Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop := implb b1 b2 = true.

Definition problem_58_pre (l1 l2 : list bool) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list bool) : Prop :=
  (* Condition 1: Commonality and Completeness *)
  (forall x: bool, In x l_out <-> (In x l1 /\ In x l2)) /\

  (* Condition 2: Ordered *)
  Sorted bool_le l_out /\

  (* Condition 3: Uniqueness *)
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [true; false; false; false; true; false; false; true; false; true; false; false]
    [true; false; false; false; true; false; false; true; false; true; false; false]
    [false; true].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x.
    destruct x; simpl; tauto.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      repeat constructor.
    + (* NoDup *)
      repeat constructor; simpl; intuition discriminate.
Qed.