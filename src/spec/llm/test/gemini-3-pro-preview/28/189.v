Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_newlines : concatenate_spec ["hello
world"; "this
string
has
multiple
newlines"] "hello
worldthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.