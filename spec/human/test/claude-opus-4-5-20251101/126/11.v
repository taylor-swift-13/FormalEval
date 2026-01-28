Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_example : problem_126_spec [1; 2; 3; 3; 3; 4] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    exfalso.
    inversion H as [| a l' Hsorted Hrel Heq].
    inversion Hsorted as [| a' l'' Hsorted' Hrel' Heq'].
    inversion Hsorted' as [| a'' l''' Hsorted'' Hrel'' Heq''].
    inversion Hrel''.
    apply Nat.lt_irrefl with (x := 3).
    assumption.
  - intros H. discriminate.
Qed.