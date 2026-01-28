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
    [0; 1; 0; 0]
    [1].
Proof.
  unfold problem_58_spec.
  split.
  - (* Part 1: Equivalence of membership *)
    intro x; split.
    + (* -> : If x in output, then x in l1 and l2 *)
      intro H.
      simpl in H.
      (* Destruct the finite possibilities in the output list *)
      (* H is a disjunction: x=1 \/ False *)
      repeat destruct H as [H|H]; subst; simpl; split; auto 20.
    + (* <- : If x in l1 and l2, then x in output *)
      intros [H1 H2].
      simpl in H1, H2.
      (* Destruct the finite possibilities in l1 to get specific values for x *)
      repeat destruct H1 as [H1|H1]; subst.
      
      (* Strategy: 
         1. Try to prove the goal assuming x matches a valid common element.
            If 'auto' succeeds (goal is true), we are done with that subgoal.
            If 'auto' fails (goal is false/hard), 'fail' triggers, 'try' catches it, and we proceed.
         2. For remaining subgoals, x must be an invalid element (not in l2).
            Prove contradiction using H2. *)
      
      (* Case 1: Handle valid common elements (1) *)
      all: try (simpl; auto; fail).
      
      (* Case 2: Handle invalid elements (2, 3) by showing H2 is false *)
      (* H2 is a disjunction of equalities. Since x is not in l2, all are false. *)
      all: exfalso; repeat destruct H2 as [H2|H2]; try lia; try contradiction.
      
  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      repeat constructor.
      all: simpl; try lia.
    + (* NoDup *)
      repeat constructor.
      (* Subgoals are negations of membership. simpl converts In to disjunctions. *)
      all: simpl; intuition lia.
Qed.