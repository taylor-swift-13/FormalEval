Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_multiline_strings :
  problem_28_spec
    ["hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hello
w14orld"; "hello
world"; "hello
world"; "1or"; "hello
w14orld"]
    "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
w14orldhello
worldhello
world1orhello
w14orld".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.