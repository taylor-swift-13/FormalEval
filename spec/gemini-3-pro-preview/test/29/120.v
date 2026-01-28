Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_chinese : filter_by_prefix_spec ["电影"; "电子"; "电话"; "邮件"; "电影"] "电" ["电影"; "电子"; "电话"; "电影"].
Proof.
  unfold filter_by_prefix_spec.
  reflexivity.
Qed.