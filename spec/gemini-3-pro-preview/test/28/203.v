Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_long : concatenate_spec ["This"; "is"; "a"; "long"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "spaces"; "or"; "characters"; "in"; "between"; "them"; "be"] "Thisisalongofstringsthatneedstobeconcatenatedintoasinglestringwithoutanyextraspacesorcharactersinbetweenthembe".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.