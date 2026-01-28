Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_97 : problem_41_pre 97.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_97_9409 : problem_41_spec 97 9409.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 97%Z) (Z.to_nat 9409%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.