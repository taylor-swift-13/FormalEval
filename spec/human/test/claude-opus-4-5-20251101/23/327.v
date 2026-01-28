Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_symbols : problem_23_spec "   

wwtens            ls   Th!s 1s 4 str1ng wtest5ymb0ls !n 1t
 " 65.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.