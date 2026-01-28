Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

(* Test case: input = 14, output = 196 *)
Example test_problem_41 : problem_41_spec 14 196.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.