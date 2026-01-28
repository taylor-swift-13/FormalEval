Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "123"; "133"; "4566"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"; "1"; "123" ] "1231334566456no
newline
this
is
a..
long
string10111213144151171123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.