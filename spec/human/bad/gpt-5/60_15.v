Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example problem_60_test_case_1 :
  let input := 1000%Z in
  let output := 500500%Z in
  problem_60_pre (Z.to_nat input) /\ problem_60_spec (Z.to_nat input) (Z.to_nat output).
Proof.
  simpl.
  split.
  - unfold problem_60_pre. simpl. apply Nat.lt_0_succ.
  - unfold problem_60_spec. simpl.
    apply Nat2Z.inj.
    rewrite !Nat2Z.inj_mul, !Nat2Z.inj_add.
    simpl. reflexivity.
Qed.