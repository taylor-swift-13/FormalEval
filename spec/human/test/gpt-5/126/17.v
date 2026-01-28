Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.le l <-> b = true.

Example problem_126_test_case_1 :
  problem_126_spec [Z.to_nat 1%Z; Z.to_nat 1%Z; Z.to_nat 2%Z; Z.to_nat 2%Z; Z.to_nat 3%Z; Z.to_nat 3%Z; Z.to_nat 4%Z] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    repeat constructor.
Qed.