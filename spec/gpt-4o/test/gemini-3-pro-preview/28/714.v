Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "chara1longcters"; "3"; ""; "66"; "8"; "the"; "9"; "10"] "1chara1longcters3668the910".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.