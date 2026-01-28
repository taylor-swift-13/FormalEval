Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["This"; "is"; "a"; "long"; "list"; "of"; "strings"; "needs"; "tto"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "or"; "characters"; "hello
world"; "in"; "between"; "them"] "Thisisalonglistofstringsneedsttobeconcatenatedintoasinglestringwithoutanyextraorcharactershello
worldinbetweenthem".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.