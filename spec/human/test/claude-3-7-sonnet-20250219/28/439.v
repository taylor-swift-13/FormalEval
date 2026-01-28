Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_hello_world :
  problem_28_spec
    ["hello
world"; "jum"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multiple
newlines"]
    "hello
worldjumthis
string
has
multiple
newlinesjumpsthis
string
has
multiple
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.