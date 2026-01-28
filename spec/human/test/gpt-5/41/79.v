Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_87 : problem_41_pre 87.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_87_7569 : problem_41_spec 87 7569.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 87%Z) (Z.to_nat 7569%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.