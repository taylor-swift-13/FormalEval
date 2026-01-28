Require Import Arith.
Require Import ZArith.

Open Scope Z_scope.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

Example problem_41_example : problem_41_spec 31 961.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.