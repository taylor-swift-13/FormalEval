Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["123"; "133"; "4566"; "456no
this
is
a..
long
string"; "10"; "11"; "12"; "144"; "15"; "1"; "17"; "15"]
  "1231334566456no
this
is
a..
long
string1011121441511715".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.