Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_newlines :
  problem_28_spec
    ["hello
world"; "this
e
newlines"; "jumps"; "dDywneedsto2🦌eepuledstg"; "this
string
has
multipule
newlines"; "hello
world"; "aa"; "this
string
has
mulntiple
newlines"; "this
string
has
mulntiple
newlines"]
    "hello
worldthis
e
newlinesjumpsdDywneedsto2🦌eepuledstgthis
string
has
multipule
newlineshello
worldaathis
string
has
mulntiple
newlinesthis
string
has
mulntiple
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.