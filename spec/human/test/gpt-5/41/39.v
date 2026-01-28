Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_21 : problem_41_pre 21.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_21_441 : problem_41_spec 21 441.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 21%Z) (Z.to_nat 441%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.