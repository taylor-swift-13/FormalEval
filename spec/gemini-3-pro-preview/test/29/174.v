Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix : filter_by_prefix_spec ["123"; "aabc1"; "abc"; "ABC"; "ab1c"; "_abc"; "abc_"; "abc1"; "1abc"] "a" ["aabc1"; "abc"; "ab1c"; "abc_"; "abc1"].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.