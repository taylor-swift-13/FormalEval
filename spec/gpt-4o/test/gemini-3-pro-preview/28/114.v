Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines : concatenate_spec ["hello
world"; "this
string
has
multiple
newlines"; "jumps"] "hello
worldthis
string
has
multiple
newlinesjumps".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.