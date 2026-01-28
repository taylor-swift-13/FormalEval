Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_19 : problem_41_pre 19.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_19_361 : problem_41_spec 19 361.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 19%Z) (Z.to_nat 361%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.