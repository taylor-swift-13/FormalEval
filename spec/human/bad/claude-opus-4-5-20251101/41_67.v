Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

(* Test case: input = 998, output = 996004 *)
Example test_problem_41 : problem_41_spec 998 996004.
Proof.
  unfold problem_41_spec.
  native_compute.
  reflexivity.
Qed.