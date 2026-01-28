Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "🦁"%string; "🦊"%string; "🐼🐼"%string; "🐨"%string; "🐯"%string; "🦛"%string; "🦌"%string; "between"%string; "🐻Dywneedst"%string; "🦉"%string; "789"%string; "🦜"%string; "🐢"%string] ("🐻🦁🦊🐼🐼🐨🐯🦛🦌between🐻Dywneedst🦉789🦜🐢"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.