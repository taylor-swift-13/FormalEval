Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_large_multiline :
  problem_28_spec
    ["lthis
string
has
multipule
newllHello, W,orld!ines"; "this
string
has
multiple
newlines"; "lthis
string
has
multipule
newlines"; "hello
world"; "this
string
has
mulntiple
newlines"; "this
string
has
mulntiple
newlines"] 
    "lthis
string
has
multipule
newllHello, W,orld!inesthis
string
has
multiple
newlineslthis
string
has
multipule
newlineshello
worldthis
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