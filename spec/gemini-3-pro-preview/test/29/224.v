Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Definition input_str := "foot" ++ String (ascii_of_nat 9) (String (ascii_of_nat 9) "hiills").

Example test_filter_by_prefix_tab : filter_by_prefix_spec [input_str] "foothills" [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.