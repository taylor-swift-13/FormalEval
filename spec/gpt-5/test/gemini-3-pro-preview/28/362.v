Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["This"; "is"; "a"; "long"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "woHwod"; "spaces"; "or"; "characters"; "in"; "between"; "them"; "be"] "ThisisalongofstringsthatneedstobeconcatenatedintoasinglestringwithoutwoHwodspacesorcharactersinbetweenthembe".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.