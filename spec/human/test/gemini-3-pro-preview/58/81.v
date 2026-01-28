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
    [100; 101; 102; 103; 104; 105; 106; 107; 108]
    [1; 2; 3; 1; 2]
    [].
Proof.
  unfold problem_58_spec.
  split.
  - intro x; split.
    + intro H. inversion H.
    + intros [H1 H2].
      simpl in H1.
      repeat destruct H1 as [H1|H1]; subst;
      simpl in H2;
      repeat destruct H2 as [H2|H2]; try lia; try contradiction.
  - split.
    + constructor.
    + constructor.
Qed.