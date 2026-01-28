Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec
    ["123"; "133"; "456"; "456no
newline
this
is
a..
long
string"; "abc878Dr🦛9d"; "10"; "3jupmps"; "11"; "12"; "13"; "144"; "15"; "1"; "abc8789d"; "15"]
    "123133456456no
newline
this
is
a..
long
stringabc878Dr🦛9d103jupmps111213144151abc8789d15".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.