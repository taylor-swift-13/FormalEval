Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long : concatenate_spec ["This"; "is"; "a"; "long"; "list"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "without"; "any"; "extra"; "spaces"; "$"; "or"; "characters"; "in"; "between"; "them"] "Thisisalonglistofstringsthatneedstobeconcatenatedintoasinglewithoutanyextraspaces$orcharactersinbetweenthem".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.