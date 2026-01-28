Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_strings : concatenate_spec ["python"; "is"; "pythonhello"; "a"; "pyothonhello"; "pythgreat789on"; "great"; "language"; "is"; "language"] "pythonispythonhelloapyothonhellopythgreat789ongreatlanguageislanguage".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.