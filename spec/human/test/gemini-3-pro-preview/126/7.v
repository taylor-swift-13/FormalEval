Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example test_case : problem_126_spec [] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _.
    reflexivity.
  - intros _.
    apply Sorted_nil.
Qed.