Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_hello :
  problem_23_spec "Hello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld!" 88.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.