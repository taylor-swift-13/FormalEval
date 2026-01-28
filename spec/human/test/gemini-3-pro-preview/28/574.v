Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "🐻"; "🦁"; "🦊"; "🐼"; "woodchuck"; "🐨"; "🐯"; "🦛"; "🦌"; "🦢"; "9"; "🦉"; "🦜"; "no
newline
this
is
a..
long
string🐢"; "🦌"; "🦁"; "woodchuck"; "🐨" ] "🐻🦁🦊🐼woodchuck🐨🐯🦛🦌🦢9🦉🦜no
newline
this
is
a..
long
string🐢🦌🦁woodchuck🐨".
Proof.
  unfold problem_28_spec.
  reflexivity.
Qed.