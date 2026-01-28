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
(* Input: strings = ["hello"; "world"; "python"; "numpy"; "pandas"], substring = "py" *)
(* Output: result = ["python"; "numpy"] *)

Example test_filter_example : filter_by_substring_spec ["hello"; "world"; "python"; "numpy"; "pandas"] "py" ["python"; "numpy"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip.
  - intros [p [s H]]. repeat (destruct p; simpl in H; try discriminate).
  - apply filter_skip.
    + intros [p [s H]]. repeat (destruct p; simpl in H; try discriminate).
    + apply filter_keep.
      * exists "", "thon". reflexivity.
      * apply filter_keep.
        -- exists "num", "". reflexivity.
        -- apply filter_skip.
           ++ intros [p [s H]]. repeat (destruct p; simpl in H; try discriminate).
           ++ apply filter_nil.
Qed.