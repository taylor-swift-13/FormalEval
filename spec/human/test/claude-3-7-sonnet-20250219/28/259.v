Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_multiple_newlines :
  problem_28_spec 
    ["1"; "this
string
has
multiple
newleines"; ""; "3"; "abcdef"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "5"]
    "1this
string
has
multiple
newleines3abcdef456789105".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.