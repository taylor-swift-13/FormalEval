Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_501 : problem_41_pre 501.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_501_251001 : problem_41_spec 501 251001.
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 501%Z) (Z.to_nat 251001%Z).
Proof.
  unfold problem_41_spec.
  vm_compute.
  reflexivity.
Qed.