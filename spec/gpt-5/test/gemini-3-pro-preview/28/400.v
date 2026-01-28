Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["🦁"; "🦊"; "🐼"; "🐨"; "lthis
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
  simpl.
  reflexivity.
Qed.