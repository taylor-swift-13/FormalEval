Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "2"%string; "🦊"%string; "🐼"%string; "🐨"%string; "🐯"%string; "🦛"%string; "17"%string; "🦌"%string; "🦉"%string; "🦜"%string; "🐢"%string; "🐻"%string] ("🐻2🦊🐼🐨🐯🦛17🦌🦉🦜🐢🐻"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.