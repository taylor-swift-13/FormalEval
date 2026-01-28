Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example problem_60_test_case_1 :
  let input := 76%Z in
  let output := 2926%Z in
  problem_60_pre (Z.to_nat input) /\ problem_60_spec (Z.to_nat input) (Z.to_nat output).
Proof.
  simpl.
  split.
  - unfold problem_60_pre. simpl. lia.
  - unfold problem_60_spec. simpl. reflexivity.
Qed.