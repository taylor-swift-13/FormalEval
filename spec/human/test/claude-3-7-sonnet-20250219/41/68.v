Require Import Arith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 57 3249.
Proof.
  simpl.
  reflexivity.
Qed.