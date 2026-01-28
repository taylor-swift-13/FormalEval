Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec [ "jum"; "this
string
has
multiple
newlines"; "jumps"; "jumps"; "jums" ] "jumthis
string
has
multiple
newlinesjumpsjumpsjums".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.