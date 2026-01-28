Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec 
  [ "t!!his
string
has
multiple
newlines"; "hello
world"; "a"; "jumps"; "t!!his
string
has
multiple
newlines" ] 
  "t!!his
string
has
multiple
newlineshello
worldajumpst!!his
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.