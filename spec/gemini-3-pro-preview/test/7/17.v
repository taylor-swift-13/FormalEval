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
(* Input: strings = ["hello"; "world"; "python"; "numpy"; "pandas"], substring = "antidisestablishmentarianismpy" *)
(* Output: result = [] *)

Example test_filter_long_substring : filter_by_substring_spec ["hello"; "world"; "python"; "numpy"; "pandas"] "antidisestablishmentarianismpy" [].
Proof.
  unfold filter_by_substring_spec.
  repeat (apply filter_skip; [ intros [p [s' H]]; repeat (destruct p; simpl in *; try discriminate) | ]).
  apply filter_nil.
Qed.