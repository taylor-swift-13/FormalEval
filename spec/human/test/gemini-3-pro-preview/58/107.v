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
    [1; 1; 1; 2; 2; 2; 3; 3; 3]
    [9; 8; 7; 6; 5]
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
      simpl in H1, H2.
      (* Destruct H1 to instantiate x, then show H2 is impossible *)
      repeat destruct H1 as [H1|H1]; subst;
      repeat destruct H2 as [H2|H2]; try lia; try contradiction.
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      constructor.
    + (* NoDup *)
      constructor.
Qed.