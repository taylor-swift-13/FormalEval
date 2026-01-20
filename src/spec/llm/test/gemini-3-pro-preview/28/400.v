Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["🦁"; "🦊"; "🐼"; "🐨"; "lthis
string
has
multipule
newlines"; "7🐯"; "🦛"; "🦌"; "multipule"; "🦉"; "🦜"; "🐢"; "🦉"] "🦁🦊🐼🐨lthis
string
has
multipule
newlines7🐯🦛🦌multipule🦉🦜🐢🦉".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.