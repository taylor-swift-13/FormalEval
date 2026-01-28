Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_24 : problem_41_pre 24.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_24_576 : problem_41_spec 24 576.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 24%Z) (Z.to_nat 576%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.