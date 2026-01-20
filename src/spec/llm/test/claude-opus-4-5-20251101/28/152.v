Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_emoji_list :
  concatenate_spec ["🦜🦜"; "🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; "🦌"; "🦢"; "🦉"; "🦜"; "🐢"; "🦉"] "🦜🦜🐻🦁🦊🐼🐨🐯🦛18🦌🦢🦉🦜🐢🦉".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.