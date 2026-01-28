Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_test_case_1 :
  problem_126_spec [Z.to_nat 1%Z; Z.to_nat 0%Z; Z.to_nat 2%Z; Z.to_nat 3%Z; Z.to_nat 4%Z] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    exfalso.
    inversion H as [| a l Hsorted Hall]; subst.
    inversion Hall as [| y l' Hy Htail]; subst.
    lia.
  - intros H.
    exfalso.
    discriminate H.
Qed.