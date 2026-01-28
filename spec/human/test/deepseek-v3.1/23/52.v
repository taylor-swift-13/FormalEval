Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_long : problem_23_spec "The quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 113.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.