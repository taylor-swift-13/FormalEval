Require Import Arith.
Require Import ZArith.

Open Scope Z_scope.

(* Definition of the specification *)
Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

(* Example proof for the test case: input = 997, output = 994009 *)
Example problem_41_example : problem_41_spec 997 994009.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.