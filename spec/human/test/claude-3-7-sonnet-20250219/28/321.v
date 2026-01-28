Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_newlines :
  problem_28_spec ["hello
world"; "this
string
has
multiple
newlines"; "1or"; "jumps"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world"]
  "hello
worldthis
string
has
multiple
newlines1orjumpshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.