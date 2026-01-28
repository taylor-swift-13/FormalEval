Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_1 : filter_by_prefix_spec ["hello"; "world"; "heworldlo"] "h" ["hello"; "heworldlo"].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.