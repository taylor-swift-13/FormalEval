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

Example test_concatenate_unicode_and_newlines :
  concatenate_spec ["🐻"; "🦊"; "quick"; "🐼"; "🐯"; "🦛"; "18"; "🦌"; "🦢"; "this
string
has
mulntiple
newlines"; "🦉"; "could🐢"; "!!"; "🐢"; "🦉"] "🐻🦊quick🐼🐯🦛18🦌🦢this
string
has
mulntiple
newlines🦉could🐢!!🐢🦉".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.