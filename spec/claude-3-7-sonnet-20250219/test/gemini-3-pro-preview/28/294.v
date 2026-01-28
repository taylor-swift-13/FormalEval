Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "3"; "4"; "5"; "Hellsingleo,6"; "7"; "9"; "10"; "5"; "🌞🌞5"; "Hellsingleo,6"] "12345Hellsingleo,679105🌞🌞5Hellsingleo,6".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.