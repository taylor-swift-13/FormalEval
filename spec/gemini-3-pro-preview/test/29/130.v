Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_kilometer : filter_by_prefix_spec [] "Kilometer" [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.