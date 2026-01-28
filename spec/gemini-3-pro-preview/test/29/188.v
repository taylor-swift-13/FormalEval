Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_filmbu : filter_by_prefix_spec ["f"; "i"; "l"; "m"; "b"; "u"] "" ["f"; "i"; "l"; "m"; "b"; "u"].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.