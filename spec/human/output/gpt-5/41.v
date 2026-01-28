Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_pre_holds_2 : problem_41_pre 2.
Proof.
  unfold problem_41_pre.
  exact I.
Qed.

Example problem_41_spec_holds_2_4 : problem_41_spec 2 4.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Example problem_41_spec_holds_Z_test :
  problem_41_spec (Z.to_nat 2%Z) (Z.to_nat 4%Z).
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.