Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_58 : problem_41_pre 58.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_58_3364 : problem_41_spec 58 3364.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 58%Z) (Z.to_nat 3364%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.