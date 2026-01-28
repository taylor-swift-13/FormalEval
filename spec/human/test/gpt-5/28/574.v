Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "🦁"%string; "🦊"%string; "🐼"%string; "woodchuck"%string; "🐨"%string; "🐯"%string; "🦛"%string; "🦌"%string; "🦢"%string; "9"%string; "🦉"%string; "🦜"%string; "no
newline
this
is
a..
long
string🐢"%string; "🦌"%string; "🦁"%string; "woodchuck"%string; "🐨"%string]
("🐻🦁🦊🐼woodchuck🐨🐯🦛🦌🦢9🦉🦜no
newline
this
is
a..
long
string🐢🦌🦁woodchuck🐨"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.