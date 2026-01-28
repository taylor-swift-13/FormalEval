Require Import Arith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 996 992016.
Proof.
  simpl.
  unfold problem_41_spec.
  (* Instead of relying on simpl, do a direct rewrite *)
  replace (992016) with (996 * 996).
  - reflexivity.
  - reflexivity.
Qed.