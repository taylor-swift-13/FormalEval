Require Import Arith.
Require Import ZArith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_84 : problem_41_pre 84.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_84_7056 : problem_41_spec 84 7056.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 84%Z) (Z.to_nat 7056%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.