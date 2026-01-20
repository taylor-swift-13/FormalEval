Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_long :
  Spec ["This"; "is"; "a"; "long"; "list"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "spaces"; "or"; "characters"; "in"; "between"; "them"]
       "Thisisalonglistofstringsthatneedstobeconcatenatedintoasinglestringwithoutanyextraspacesorcharactersinbetweenthem".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.