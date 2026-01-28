Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "123"; "133"; "4566"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"; "456no
newline
this
is
a..
long
string" ] "1231334566456no
newline
this
is
a..
long
string1011121314415117456no
newline
this
is
a..
long
string".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.