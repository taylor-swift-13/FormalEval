Require Import ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 10000 100000000.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.