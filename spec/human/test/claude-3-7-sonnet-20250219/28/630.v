Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_multiline_string :
  problem_28_spec
    ["chara1longHello, Woworldrld!rs"; "hello
world"; "characters"; "no
newline
this
is
a..
long
string"; "has"; "this
string
has
multiple
newlines"]
    "chara1longHello, Woworldrld!rshello
worldcharactersno
newline
this
is
a..
long
stringhasthis
string
has
multiple
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.