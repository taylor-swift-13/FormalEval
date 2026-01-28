Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long: concatenate_spec ["This"; "is"; "a"; "long"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "woHwod"; "spaces"; "or"; "characters"; "in"; "between"; "them"; "be"] "ThisisalongofstringsthatneedstobeconcatenatedintoasinglestringwithoutwoHwodspacesorcharactersinbetweenthembe".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.