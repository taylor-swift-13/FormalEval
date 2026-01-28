Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

(* Test case: input = 1003, output = 1006009 *)
Example test_problem_41 : problem_41_spec 1003 1006009.
Proof.
  unfold problem_41_spec.
  native_compute.
  reflexivity.
Qed.