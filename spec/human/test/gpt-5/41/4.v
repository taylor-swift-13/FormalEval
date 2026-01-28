Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_8 : problem_41_pre 8.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_8_64 : problem_41_spec 8 64.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 8%Z) (Z.to_nat 64%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.