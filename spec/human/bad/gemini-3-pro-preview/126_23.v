Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example test_case : problem_126_spec [1; 0; 2; 3; 4] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    inversion H; subst.
    inversion H2; subst.
    match goal with
    | H : Nat.lt _ 0 |- _ => inversion H
    end.
  - intros H.
    discriminate.
Qed.