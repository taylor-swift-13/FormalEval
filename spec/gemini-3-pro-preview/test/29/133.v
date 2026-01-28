Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_complex : filter_by_prefix_spec [""%string; String (ascii_of_nat 10) ""%string; String (ascii_of_nat 9) ""%string; "a"%string; "ab"%string; "abc"%string; "abcde"%string] "ampABCersand"%string [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.