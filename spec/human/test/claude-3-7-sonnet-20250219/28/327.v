Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_multiline_strings :
  problem_28_spec
    ["t!!shis
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "t!!his
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "jumps"]
    "t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlinesjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumps".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.