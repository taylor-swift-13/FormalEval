Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "strings"; "8"; "555"; ""; "9"; "10"; "li8Hellsingleo,st"; "5"; "6"] "1234This699★strings8555910li8Hellsingleo,st56".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.