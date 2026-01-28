Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.le l <-> b = true.

Example test_case : problem_126_spec [1; 1; 2; 3; 4] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _.
    reflexivity.
  - intros _.
    repeat apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
    + apply HdRel_cons. repeat constructor.
    + apply HdRel_cons. repeat constructor.
    + apply HdRel_cons. repeat constructor.
    + apply HdRel_cons. repeat constructor.
Qed.