Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_complex :
  problem_23_spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" 60.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.