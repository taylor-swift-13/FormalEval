Require Import Arith.
Require Import ZArith.
Require Import Lia.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_10001 : problem_41_pre (Z.to_nat 10001%Z).
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 10001%Z) (Z.to_nat 100020001%Z).
Proof.
  unfold problem_41_spec.
  rewrite <- Z2Nat.inj_mul by lia.
  assert (H : 100020001%Z = 10001%Z * 10001%Z) by reflexivity.
  rewrite H.
  reflexivity.
Qed.