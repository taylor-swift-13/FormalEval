Require Import Arith.
Require Import ZArith.

Open Scope Z_scope.

(* Definition of the specification *)
Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

(* Example proof for the test case: input = 23, output = 529 *)
Example problem_41_example : problem_41_spec 23 529.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.