Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "6"; "7"; "1or"; "8"; "9"] "string1232🦌4671or89".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.