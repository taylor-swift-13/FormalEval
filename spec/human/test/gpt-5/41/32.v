Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_498 : problem_41_pre 498.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_498_248004 : problem_41_spec 498 248004.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 498%Z) (Z.to_nat 248004%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.