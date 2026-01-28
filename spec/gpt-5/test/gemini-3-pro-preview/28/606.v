Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["This"; "is"; "a"; "long"; "list"; "of"; "strings"; "needs"; "tto"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "or"; "characters"; "hello
world"; "in"; "between"; "them"] "Thisisalonglistofstringsneedsttobeconcatenatedintoasinglestringwithoutanyextraorcharactershello
worldinbetweenthem".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.