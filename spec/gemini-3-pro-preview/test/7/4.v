Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

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

Example test_filter_basic : filter_by_substring_spec ["grunt"; "trumpet"; "prune"; "gruesome"] "run" ["grunt"; "prune"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "g", "t". reflexivity.
  - apply filter_skip.
    + intros [pre [suf H]].
      do 10 (destruct pre; simpl in H; [try discriminate | ]).
      discriminate.
    + apply filter_keep.
      * exists "p", "e". reflexivity.
      * apply filter_skip.
        { intros [pre [suf H]].
          do 10 (destruct pre; simpl in H; [try discriminate | ]).
          discriminate. }
        { apply filter_nil. }
Qed.