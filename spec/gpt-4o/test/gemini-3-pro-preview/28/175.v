Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["1"; "2"; "3"; "4"; "5"; "6"; "★"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"] "123456★78555910list5".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.