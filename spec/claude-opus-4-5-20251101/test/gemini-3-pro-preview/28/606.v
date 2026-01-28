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

Example test_concatenate_long: concatenate_spec 
  ["This"; "is"; "a"; "long"; "list"; "of"; "strings"; "needs"; "tto"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "or"; "characters"; "hello
world"; "in"; "between"; "them"]
  "Thisisalonglistofstringsneedsttobeconcatenatedintoasinglestringwithoutanyextraorcharactershello
worldinbetweenthem".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.