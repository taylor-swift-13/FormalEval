Require Import String.
Require Import ZArith.

Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_long : problem_23_spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" 86.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.