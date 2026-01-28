Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_asdasnakj :
  problem_23_spec "asdasnakj" 9.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.