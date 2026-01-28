Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_7 : problem_41_pre 7.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_7_49 : problem_41_spec 7 49.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 7%Z) (Z.to_nat 49%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.