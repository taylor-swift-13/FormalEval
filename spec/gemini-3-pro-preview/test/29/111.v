Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_qwe : filter_by_prefix_spec [] "qwe" [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.