Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_chinese : filter_by_prefix_spec ["电电"] "电facetious" [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.