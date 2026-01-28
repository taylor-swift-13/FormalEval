Require Import Arith.
Require Import ZArith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

(* Test case: input = 26, output = 676 *)
Example test_problem_41 : problem_41_spec 26 676.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.