Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_complex : filter_by_prefix_spec ["123"; "abc"; "ABC"; "application123"; "ab1c"; "_a_bc"; "abc_"; "abc1"; "tea"; "电"] "aa" [].
Proof.
  unfold filter_by_prefix_spec.
  reflexivity.
Qed.