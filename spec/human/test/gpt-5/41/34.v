Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_102 : problem_41_pre 102.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_102_10404 : problem_41_spec 102 10404.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 102%Z) (Z.to_nat 10404%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.