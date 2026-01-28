Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_complex : filter_by_prefix_spec 
  [""; "
"; "	"; "a"; "abbatman"; "ab"; "abc"; "abcde"; "abbatman"] 
  "a电电话mpABCersand" 
  [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.