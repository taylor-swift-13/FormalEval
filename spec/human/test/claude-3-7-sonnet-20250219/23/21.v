Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_complex :
  problem_23_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.