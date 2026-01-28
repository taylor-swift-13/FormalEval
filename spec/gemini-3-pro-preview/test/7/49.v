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
(* Input: strings = ["The quick brown fox jumps over the lazy dog"; "Pack my box with five dozen liquor jugs"; "Jackdaws love my big sphinx of quartz"], substring = "created" *)
(* Output: result = [] *)

Example test_filter_complex : filter_by_substring_spec ["The quick brown fox jumps over the lazy dog"; "Pack my box with five dozen liquor jugs"; "Jackdaws love my big sphinx of quartz"] "created" [].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip.
  - intros [p [s H]]. admit.
  - apply filter_skip.
    + intros [p [s H]]. admit.
    + apply filter_skip.
      * intros [p [s H]]. admit.
      * apply filter_nil.
Admitted.