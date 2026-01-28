Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_44 : problem_41_pre 44.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_44_1936 : problem_41_spec 44 1936.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 44%Z) (Z.to_nat 1936%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.