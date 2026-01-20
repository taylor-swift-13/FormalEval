Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_with_newlines :
  Spec ["hello
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
  unfold Spec.
  simpl.
  reflexivity.
Qed.