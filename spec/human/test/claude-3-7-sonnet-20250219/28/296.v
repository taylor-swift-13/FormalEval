Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_example :
  problem_28_spec
    ["1"; "no
newline
this
is
a..
long
string"; "2"; "110"; "5🦉"; ""; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "5"]
    "1no
newline
this
is
a..
long
string21105🦉3456789105".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.