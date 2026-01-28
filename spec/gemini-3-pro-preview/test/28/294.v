Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["1"; "2"; "3"; "4"; "5"; "Hellsingleo,6"; "7"; "9"; "10"; "5"; "🌞🌞5"; "Hellsingleo,6"] "12345Hellsingleo,679105🌞🌞5Hellsingleo,6".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.