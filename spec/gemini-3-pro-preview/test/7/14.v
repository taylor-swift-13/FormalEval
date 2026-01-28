Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Specification definitions *)
Definition contains_substring (s sub : string) : Prop :=
  exists prefix suffix, s = prefix ++ sub ++ suffix.

Inductive FilterRel (sub : string) : list string -> list string -> Prop :=
| filter_nil : FilterRel sub [] []
| filter_keep : forall s l l',
    contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) (s :: l')
| filter_skip : forall s l l',
    ~ contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  FilterRel substring strings result.

(* Test case verification *)
(* Input: strings = ["earth"; "mars"; "jupiter"; "saturn"; "uranus"], substring = "s" *)
(* Output: result = ["mars"; "saturn"; "uranus"] *)

Example test_filter_planets : filter_by_substring_spec ["earth"; "mars"; "jupiter"; "saturn"; "uranus"] "s" ["mars"; "saturn"; "uranus"].
Proof.
  unfold filter_by_substring_spec.
  (* earth: skip *)
  apply filter_skip.
  { unfold contains_substring. intros [prefix [suffix H]].
    repeat (destruct prefix; simpl in H; try discriminate). }
  (* mars: keep *)
  apply filter_keep.
  { unfold contains_substring. exists "mar". exists "". reflexivity. }
  (* jupiter: skip *)
  apply filter_skip.
  { unfold contains_substring. intros [prefix [suffix H]].
    repeat (destruct prefix; simpl in H; try discriminate). }
  (* saturn: keep *)
  apply filter_keep.
  { unfold contains_substring. exists "". exists "aturn". reflexivity. }
  (* uranus: keep *)
  apply filter_keep.
  { unfold contains_substring. exists "uranu". exists "". reflexivity. }
  (* nil *)
  apply filter_nil.
Qed.