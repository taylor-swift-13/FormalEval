Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_example : problem_126_spec [1; 0; 2; 3; 4] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    inversion H as [| a l' Hsorted Hrel Heq].
    inversion Hrel as [| b l'' Hlt Heq'].
    simpl in Hlt.
    inversion Hlt.
  - intros H.
    discriminate H.
Qed.