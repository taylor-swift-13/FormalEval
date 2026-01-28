Require Import Arith.
Require Import ZArith.

Open Scope Z_scope.

Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 987654 975460423716.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.