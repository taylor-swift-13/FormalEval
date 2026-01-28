Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_complex : filter_by_prefix_spec 
  [""; " "; String (ascii_of_nat 10) EmptyString; String (ascii_of_nat 9) EmptyString; "ab"; "abc"; "abcde"; " "; String (ascii_of_nat 9) EmptyString] 
  "" 
  [""; " "; String (ascii_of_nat 10) EmptyString; String (ascii_of_nat 9) EmptyString; "ab"; "abc"; "abcde"; " "; String (ascii_of_nat 9) EmptyString].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.