Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_100 : problem_41_pre 100.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_100_10000 : problem_41_spec 100 10000.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 100%Z) (Z.to_nat 10000%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.