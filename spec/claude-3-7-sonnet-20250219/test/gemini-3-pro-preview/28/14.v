Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_custom: concatenate_spec ["python"; "is"; "pythonhello"; "a"; "great"; "language"; "is"] "pythonispythonhelloagreatlanguageis".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.