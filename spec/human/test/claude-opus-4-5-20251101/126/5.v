Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_example : problem_126_spec [1; 2; 3; 4; 5; 6; 7] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    apply Sorted_cons. apply Sorted_cons. apply Sorted_cons.
    apply Sorted_cons. apply Sorted_cons. apply Sorted_cons.
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
    + apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
    + apply HdRel_cons. auto.
Qed.