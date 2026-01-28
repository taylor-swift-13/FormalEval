Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["This"; "is"; "a"; "long"; "of"; "strings"; "that"; "needs"; "to"; "be"; "concatenated"; "into"; "a"; "single"; "string"; "without"; "any"; "extra"; "spaces"; "or"; "characters"; "in"; "between"; "them"; "be"]
    "Thisisalongofstringsthatneedstobeconcatenatedintoasinglestringwithoutanyextraspacesorcharactersinbetweenthembe".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.