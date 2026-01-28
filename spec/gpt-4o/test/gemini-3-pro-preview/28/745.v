Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_long : concatenate_spec ["123"; "456"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"] "12345678910111214151617".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.