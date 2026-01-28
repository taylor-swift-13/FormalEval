Require Import Arith.
Require Import ZArith.

Open Scope Z_scope.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

(* Test case: input = 1000000000, output = 1000000000000000000 *)
Example test_problem_41 : problem_41_spec 1000000000 1000000000000000000.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.