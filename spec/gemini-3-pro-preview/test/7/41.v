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
(* Input: strings = ["abcdefg"], substring = "" *)
(* Output: result = ["abcdefg"] *)

Example test_filter_empty_substring : filter_by_substring_spec ["abcdefg"] "" ["abcdefg"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - unfold contains_substring.
    exists "", "abcdefg".
    simpl.
    reflexivity.
  - apply filter_nil.
Qed.